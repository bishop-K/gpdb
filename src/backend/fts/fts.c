/*-------------------------------------------------------------------------
 *
 * fts.c
 *	  Process under QD postmaster polls the segments on a periodic basis
 *    or at the behest of QEs.
 *
 * Maintains an array in shared memory containing the state of each segment.
 *
 * Portions Copyright (c) 2005-2010, Greenplum Inc.
 * Portions Copyright (c) 2011, EMC Corp.
 * Portions Copyright (c) 2012-Present Pivotal Software, Inc.
 *
 *
 * IDENTIFICATION
 *	    src/backend/fts/fts.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <unistd.h>

/* These are always necessary for a bgworker */
#include "miscadmin.h"
#include "postmaster/bgworker.h"
#include "storage/ipc.h"
#include "storage/latch.h"
#include "storage/lwlock.h"
#include "storage/proc.h"
#include "storage/shmem.h"

#include "access/xact.h"
#include "catalog/indexing.h"
#include "libpq/pqsignal.h"
#include "cdb/cdbvars.h"
#include "libpq-int.h"
#include "cdb/cdbfts.h"
#include "postmaster/fts.h"
#include "postmaster/ftsprobe.h"
#include "postmaster/postmaster.h"
#include "utils/builtins.h"
#include "utils/faultinjector.h"
#include "utils/fmgroids.h"
#include "utils/memutils.h"
#include "utils/snapmgr.h"

#include "catalog/gp_configuration_history.h"
#include "catalog/gp_segment_config.h"

#include "replication/walsender.h"
#include "replication/walsender_private.h"
#include "tcop/tcopprot.h" /* quickdie() */

bool am_ftsprobe = false;
bool am_ftshandler = false;

extern bool gp_enable_master_autofailover;

#define MAX_ENTRYDB_COUNT 2

/*
 * STRUCTURES
 */

typedef struct MasterInfo
{
	int16 port;
	char *hostname;
	char *address;
	char *datadir;
} MasterInfo;
/*
 * STATIC VARIABLES
 */
static bool skipFtsProbe = false;
static volatile pid_t *shmFtsProbePID;

static volatile bool probe_requested = false;
static volatile sig_atomic_t got_SIGHUP = false;

/*
 * FUNCTION PROTOTYPES
 */
static void FtsLoop(void);

static CdbComponentDatabases *readCdbComponentInfoAndUpdateStatus();

/*=========================================================================
 * HELPER FUNCTIONS
 */
/* SIGHUP: set flag to reload config file */
static void
sigHupHandler(SIGNAL_ARGS)
{
	got_SIGHUP = true;

	if (MyProc)
		SetLatch(&MyProc->procLatch);
}

/* SIGINT: set flag to indicate a FTS scan is requested */
static void
sigIntHandler(SIGNAL_ARGS)
{
	probe_requested = true;

	if (MyProc)
		SetLatch(&MyProc->procLatch);
}

void
FtsProbeShmemInit(void)
{
	if (IsUnderPostmaster)
		return;

	shmFtsProbePID = (volatile pid_t*)ShmemAlloc(sizeof(*shmFtsProbePID));
	*shmFtsProbePID = 0;
}

pid_t
FtsProbePID(void)
{
	return *shmFtsProbePID;
}

bool
FtsProbeStartRule(Datum main_arg)
{
	/* we only start fts probe on master when -E is specified */
	if (IsUnderMasterDispatchMode())
		return true;

	/* start master prober */
	if (gp_enable_master_autofailover &&
		GpIdentity.segindex == 0 &&
		shmFtsControl && shmFtsControl->startMasterProber)
		return true;

	return false;
}

/*
 * FtsProbeMain
 */
void
FtsProbeMain(Datum main_arg)
{
	*shmFtsProbePID = MyProcPid;
	am_ftsprobe = true;

	/*
	 * reread postgresql.conf if requested
	 */
	pqsignal(SIGHUP, sigHupHandler);
	pqsignal(SIGINT, sigIntHandler);

	/*
	 * CDB: Catch program error signals.
	 *
	 * Save our main thread-id for comparison during signals.
	 */
	main_tid = pthread_self();

#ifdef SIGSEGV
	pqsignal(SIGSEGV, CdbProgramErrorHandler);
#endif

	/* We're now ready to receive signals */
	BackgroundWorkerUnblockSignals();

	/* Connect to our database */
	BackgroundWorkerInitializeConnection(DB_FOR_COMMON_ACCESS, NULL);

	/* main loop */
	FtsLoop();

	/* One iteration done, go away */
	proc_exit(0);
}

/*
 * Populate cdb_component_dbs object by reading from catalog.  Use
 * probeContext instead of current memory context because current
 * context will be destroyed by CommitTransactionCommand().
 */
static
CdbComponentDatabases *readCdbComponentInfoAndUpdateStatus()
{
	int i;
	CdbComponentDatabases *cdbs = cdbcomponent_getCdbComponents();

	for (i=0; i < cdbs->total_segment_dbs; i++)
	{
		CdbComponentDatabaseInfo *segInfo = &cdbs->segment_db_info[i];
		uint8	segStatus = 0;

		if (!SEGMENT_IS_ALIVE(segInfo))
			FTS_STATUS_SET_DOWN(segStatus);

		ftsProbeInfo->status[segInfo->config->dbid] = segStatus;
	}

	/*
	 * Initialize fts_stausVersion after populating the config details in
	 * shared memory for the first time after FTS startup.
	 */
	if (ftsProbeInfo->status_version == 0)
	{
		ftsProbeInfo->status_version++;
		writeGpSegConfigToFTSFiles();
	}

	return cdbs;
}

void
probeWalRepUpdateConfig(int16 dbid, int16 segindex, char role,
						bool IsSegmentAlive, bool IsInSync)
{
	AssertImply(IsInSync, IsSegmentAlive);

	/*
	 * Insert new tuple into gp_configuration_history catalog.
	 */
	{
		Relation histrel;
		HeapTuple histtuple;
		Datum histvals[Natts_gp_configuration_history];
		bool histnulls[Natts_gp_configuration_history] = { false };
		char desc[SQL_CMD_BUF_SIZE];

		histrel = heap_open(GpConfigHistoryRelationId,
							RowExclusiveLock);

		histvals[Anum_gp_configuration_history_time-1] =
				TimestampTzGetDatum(GetCurrentTimestamp());
		histvals[Anum_gp_configuration_history_dbid-1] =
				Int16GetDatum(dbid);
		snprintf(desc, sizeof(desc),
				 "FTS: update role, status, and mode for dbid %d with contentid %d to %c, %c, and %c",
				 dbid, segindex, role,
				 IsSegmentAlive ? GP_SEGMENT_CONFIGURATION_STATUS_UP :
				 GP_SEGMENT_CONFIGURATION_STATUS_DOWN,
				 IsInSync ? GP_SEGMENT_CONFIGURATION_MODE_INSYNC :
				 GP_SEGMENT_CONFIGURATION_MODE_NOTINSYNC
			);
		histvals[Anum_gp_configuration_history_desc-1] =
				CStringGetTextDatum(desc);
		histtuple = heap_form_tuple(RelationGetDescr(histrel), histvals, histnulls);
		simple_heap_insert(histrel, histtuple);
		CatalogUpdateIndexes(histrel, histtuple);

		SIMPLE_FAULT_INJECTOR("fts_update_config");

		heap_close(histrel, RowExclusiveLock);
	}

	/*
	 * Find and update gp_segment_configuration tuple.
	 */
	{
		Relation configrel;

		HeapTuple configtuple;
		HeapTuple newtuple;

		Datum configvals[Natts_gp_segment_configuration];
		bool confignulls[Natts_gp_segment_configuration] = { false };
		bool repls[Natts_gp_segment_configuration] = { false };

		ScanKeyData scankey;
		SysScanDesc sscan;

		configrel = heap_open(GpSegmentConfigRelationId,
							  RowExclusiveLock);

		ScanKeyInit(&scankey,
					Anum_gp_segment_configuration_dbid,
					BTEqualStrategyNumber, F_INT2EQ,
					Int16GetDatum(dbid));
		sscan = systable_beginscan(configrel, GpSegmentConfigDbidIndexId,
								   true, NULL, 1, &scankey);

		configtuple = systable_getnext(sscan);

		if (!HeapTupleIsValid(configtuple))
		{
			elog(ERROR, "FTS cannot find dbid=%d in %s", dbid,
				 RelationGetRelationName(configrel));
		}

		configvals[Anum_gp_segment_configuration_role-1] = CharGetDatum(role);
		repls[Anum_gp_segment_configuration_role-1] = true;

		configvals[Anum_gp_segment_configuration_status-1] =
			CharGetDatum(IsSegmentAlive ? GP_SEGMENT_CONFIGURATION_STATUS_UP :
										GP_SEGMENT_CONFIGURATION_STATUS_DOWN);
		repls[Anum_gp_segment_configuration_status-1] = true;

		configvals[Anum_gp_segment_configuration_mode-1] =
			CharGetDatum(IsInSync ? GP_SEGMENT_CONFIGURATION_MODE_INSYNC :
						 GP_SEGMENT_CONFIGURATION_MODE_NOTINSYNC);
		repls[Anum_gp_segment_configuration_mode-1] = true;

		newtuple = heap_modify_tuple(configtuple, RelationGetDescr(configrel),
									 configvals, confignulls, repls);
		simple_heap_update(configrel, &configtuple->t_self, newtuple);
		CatalogUpdateIndexes(configrel, newtuple);

		systable_endscan(sscan);
		pfree(newtuple);

		heap_close(configrel, RowExclusiveLock);
	}
}

/*
 * We say the standby is alive when one of the wal-sender processes is alive.
 */
static
bool standbyIsInSync()
{
	bool inSync = false;
	int i;

	LWLockAcquire(SyncRepLock, LW_SHARED);
	for (i = 0; i < max_wal_senders; i++)
	{
		if (WalSndCtl->walsnds[i].pid != 0)
		{
			inSync = (WalSndCtl->walsnds[i].state == WALSNDSTATE_STREAMING);
			break;
		}
	}
	LWLockRelease(SyncRepLock);

	return inSync;
}

/*
 * Master should notify standby before start master prober
 */
static
bool notifyStandbyMasterProberDbid(CdbComponentDatabases *cdbs, int dbid)
{
	CdbComponentDatabaseInfo *standby = NULL;
	char proberMessage[30];
	char message[FTS_MSG_MAX_LEN];
	int i;

	for (i = 0; i < cdbs->total_entry_dbs; i++)
	{
		CdbComponentDatabaseInfo *cdb = &cdbs->entry_db_info[i];
		if (cdb->config->role != GP_SEGMENT_CONFIGURATION_ROLE_PRIMARY)
		{
			standby = cdb;
			break;
		}
	}

	if (standby == NULL || !standbyIsInSync())
		return false;

	snprintf(proberMessage, sizeof(proberMessage), FTS_MSG_NEW_MASTER_PROBER_FMT, dbid);
	snprintf(message, FTS_MSG_MAX_LEN, FTS_MSG_FORMAT,
			proberMessage,
			standby->config->dbid,
			standby->config->segindex);
	return FtsWalRepMessageOneSegment(standby, message);
}

/*
 * Send master and standby information to segment to start master prober
 */
static
bool notifySegmentStartMasterProber(CdbComponentDatabases *cdbs, bool restart)
{
	char proberMessage[MASTER_PROBER_MESSAGE_MAXLEN];
	char message[FTS_MSG_MAX_LEN];
	struct GpSegConfigEntry *master = NULL;
	struct GpSegConfigEntry *standby = NULL;
	int i;

	for (i = 0; i < cdbs->total_entry_dbs; i++)
	{
		CdbComponentDatabaseInfo *cdb = &cdbs->entry_db_info[i];
		struct GpSegConfigEntry *cdbConfig = cdb->config;
		if (cdbConfig->preferred_role == GP_SEGMENT_CONFIGURATION_ROLE_PRIMARY)
			master = cdbConfig;
		else
			standby = cdbConfig;
	}

	if (!standby || !master)
		return false;

	/*
	 * START_MASTER_PROBER;<is_restart>;<dbid>;<preferred_role>;<role>;<hostname>;<address>;
	 * <port>;<dbid>;<preferred_role>;<role>;<hostname>;<address>;<port>
	 */
	snprintf(proberMessage, MASTER_PROBER_MESSAGE_MAXLEN,
			FTS_MSG_START_MASTER_PROBER_FMT,
			restart,
			master->dbid, master->preferred_role, master->role,
			master->hostname, master->address, master->port,
			standby->dbid, standby->preferred_role, standby->role,
			standby->hostname, standby->address, standby->port);
	snprintf(message, FTS_MSG_MAX_LEN, FTS_MSG_FORMAT,
			proberMessage,
			cdbs->segment_db_info[0].config->dbid,
			cdbs->segment_db_info[0].config->segindex);
	return FtsWalRepMessageOneSegment(&cdbs->segment_db_info[0], message);
}

/*
 * Start master prober
 */
static
bool startMasterProber(CdbComponentDatabases *cdbs, bool restart)
{
	/* start the master prober on the primary segment of content 0 */
	int masterProberDbid = cdbs->segment_db_info[0].config->dbid;

	if (shmFtsControl->masterProberDBID != masterProberDbid)
	{
		if (!notifyStandbyMasterProberDbid(cdbs, masterProberDbid))
		{
			elog(LOG, "FTS: failed to notify standby the master prober");
			return false;
		}

		shmFtsControl->masterProberDBID = masterProberDbid;
	}

	if (!notifySegmentStartMasterProber(cdbs, restart))
	{
		elog(LOG, "FTS: failed to start master prober");
		return false;
	}

	elog(LOG, "FTS: start master prober on segment %d, is restart: %d", masterProberDbid, restart);
	return true;
}

static bool
ftsMessageNextParam(char **cpp, char **npp)
{
	*cpp = *npp;
	if (!*cpp)
		return false;

	*npp = strchr(*npp, ';');
	if (*npp)
	{
		**npp = '\0';
		++*npp;
	}
	return true;
}

/*
 * Parse start message and insert into gp_segment_configuration
 */
static void
masterProberConfigInsert(Relation configrel, char **query)
{
	HeapTuple	configtuple;
	Datum		values[Natts_gp_segment_configuration];
	bool			isnull[Natts_gp_segment_configuration] = { false };
	char			role;
	char			preferredRole;
	int16		dbid;
	const char	*hostname;
	const char	*address;
	int32		port;
	char			*cp;
	bool			ret;

	/*
	 * START_MASTER_PROBER;<dbid>;<preferred_role>;<role>;<hostname>;<address>;
	 * <port>;<dbid>;<preferred_role>;<role>;<hostname>;<address>;<port>
	 */
	ret = ftsMessageNextParam(&cp, query);
	Assert(ret);
	dbid = (int16)strtol(cp, NULL, 10);

	ret = ftsMessageNextParam(&cp, query);
	Assert(ret);
	preferredRole = *cp;

	ret = ftsMessageNextParam(&cp, query);
	Assert(ret);
	role = *cp;

	ret = ftsMessageNextParam(&cp, query);
	Assert(ret);
	hostname = cp;

	ret = ftsMessageNextParam(&cp, query);
	Assert(ret);
	address = cp;

	ret = ftsMessageNextParam(&cp, query);
	Assert(ret);
	port = (int32)strtol(cp, NULL, 10);

	values[Anum_gp_segment_configuration_content - 1] = Int16GetDatum(-1);
	values[Anum_gp_segment_configuration_mode - 1] = CharGetDatum('s');
	values[Anum_gp_segment_configuration_status - 1] = CharGetDatum('u');
	values[Anum_gp_segment_configuration_datadir - 1] = CStringGetTextDatum("");

	values[Anum_gp_segment_configuration_preferred_role - 1] = CharGetDatum(preferredRole);
	values[Anum_gp_segment_configuration_dbid - 1] = Int16GetDatum(dbid);
	values[Anum_gp_segment_configuration_role - 1] = CharGetDatum(role);
	values[Anum_gp_segment_configuration_port - 1] = Int32GetDatum(port);
	values[Anum_gp_segment_configuration_hostname - 1] = CStringGetTextDatum(hostname);
	values[Anum_gp_segment_configuration_address - 1] = CStringGetTextDatum(address);

	configtuple = heap_form_tuple(RelationGetDescr(configrel), values, isnull);
	simple_heap_insert(configrel, configtuple);
	CatalogUpdateIndexes(configrel, configtuple);
	return;
}

/*
 * Clear gp_segment_configuration
 */
static
void masterProberConfigClear(Relation configrel)
{
	HeapTuple	tup;
	SysScanDesc scan;

	scan = systable_beginscan(configrel, InvalidOid, false, NULL, 0, NULL);
	while (HeapTupleIsValid(tup = systable_getnext(scan)))
		simple_heap_delete(configrel, &tup->t_self);

	systable_endscan(scan);
}

/*
 * Insert master and standby information into gp_segment_configuration
 */
static
void masterProberConfigInit()
{
	Relation configrel;
	ResourceOwner save;

	char	   *message = pstrdup(shmFtsControl->masterProberMessage);
	char	   *cp;

	ftsMessageNextParam(&cp, &message);
	Assert(strncmp(cp, FTS_MSG_START_MASTER_PROBER,
				   strlen(FTS_MSG_START_MASTER_PROBER)) == 0);
	ftsMessageNextParam(&cp, &message);

	save = CurrentResourceOwner;
	StartTransactionCommand();
	GetTransactionSnapshot();

	configrel = heap_open(GpSegmentConfigRelationId, RowExclusiveLock);
	masterProberConfigClear(configrel);
	masterProberConfigInsert(configrel, &message);
	masterProberConfigInsert(configrel, &message);
	heap_close(configrel, RowExclusiveLock);

	CommitTransactionCommand();
	CurrentResourceOwner = save;
}

/*
 * Check if master and standby information changed
 */
static
bool updateMasterInfomationForMasterProber(CdbComponentDatabases *cdbs, MasterInfo *masters)
{
	bool	masterInfoChanged = false;
	int		i;

	Assert(cdbs->total_entry_dbs == MAX_ENTRYDB_COUNT);

	for (i = 0; i < MAX_ENTRYDB_COUNT; i++)
	{
		struct GpSegConfigEntry *config = cdbs->entry_db_info[i].config;	

		if (masters[i].hostname == NULL ||
			strcmp(masters[i].hostname, config->hostname) != 0)
		{
			masters[i].hostname = pstrdup(config->hostname);
			masterInfoChanged = true;
		}

		if (masters[i].address == NULL ||
			strcmp(masters[i].address, config->address) != 0)
		{
			masters[i].address = pstrdup(config->address);
			masterInfoChanged = true;
		}

		if (masters[i].datadir == NULL ||
			strcmp(masters[i].datadir, config->datadir) != 0)
		{
			masters[i].datadir = pstrdup(config->datadir);
			masterInfoChanged = true;
		}

		if (masters[i].port !=  config->port)
		{
			masters[i].port = config->port;
			masterInfoChanged = true;
		}
	}

	return masterInfoChanged;
}

static
void FtsLoop()
{
	bool	updated_probe_state;
	MemoryContext probeContext = NULL, oldContext = NULL;
	time_t elapsed,	probe_start_time, timeout;
	CdbComponentDatabases *cdbs = NULL;
	bool	standbyInSync;
	bool	masterInfoChanged = true;
	bool	am_masterprober = !IS_QUERY_DISPATCHER();
	MasterInfo	*masterInfos = palloc0(sizeof(MasterInfo) * MAX_ENTRYDB_COUNT);

	probeContext = AllocSetContextCreate(TopMemoryContext,
										 "FtsProbeMemCtxt",
										 ALLOCSET_DEFAULT_INITSIZE,	/* always have some memory */
										 ALLOCSET_DEFAULT_INITSIZE,
										 ALLOCSET_DEFAULT_MAXSIZE);

	if (am_masterprober)
		masterProberConfigInit();

	while (true)
	{
		bool		has_mirrors;
		bool		masterProberStarted = false;
		int			rc;

		if (got_SIGHUP)
		{
			got_SIGHUP = false;
			ProcessConfigFile(PGC_SIGHUP);
		}

		CHECK_FOR_INTERRUPTS();

		SIMPLE_FAULT_INJECTOR("ftsLoop_before_probe");

		probe_start_time = time(NULL);

		SpinLockAcquire(&ftsProbeInfo->lock);
		ftsProbeInfo->start_count++;
		SpinLockRelease(&ftsProbeInfo->lock);

		/* Need a transaction to access the catalogs */
		StartTransactionCommand();
		cdbs = readCdbComponentInfoAndUpdateStatus();

		/* Check here gp_segment_configuration if has mirror's */
		if (am_masterprober)
			has_mirrors = gp_segment_config_has_standby();
		else
			has_mirrors = gp_segment_config_has_mirrors();

		/* close the transaction we started above */
		CommitTransactionCommand();

		/* is master or standby changed? */
		if (gp_enable_master_autofailover &&
			!am_masterprober &&
			cdbs->total_entry_dbs == MAX_ENTRYDB_COUNT)
			masterInfoChanged = updateMasterInfomationForMasterProber(cdbs, masterInfos);

		/* Reset this as we are performing the probe */
		probe_requested = false;
		skipFtsProbe = false;

		if (SIMPLE_FAULT_INJECTOR("fts_probe") == FaultInjectorTypeSkip)
			skipFtsProbe = true;

		if (skipFtsProbe || !has_mirrors)
		{
			elogif(gp_log_fts >= GPVARS_VERBOSITY_VERBOSE, LOG,
				   "skipping FTS probes due to %s",
				   !has_mirrors ? "no mirrors" : "fts_probe fault");

		}
		else
		{
			elogif(gp_log_fts == GPVARS_VERBOSITY_DEBUG, LOG,
				   "FTS: starting %s scan with %d segments and %d contents",
				   (probe_requested ? "full " : ""),
				   cdbs->total_segment_dbs,
				   cdbs->total_segments);
			/*
			 * We probe in a special context, some of the heap access
			 * stuff palloc()s internally
			 */
			oldContext = MemoryContextSwitchTo(probeContext);

			updated_probe_state = FtsWalRepMessageSegments(cdbs, am_masterprober, &masterProberStarted);

			MemoryContextSwitchTo(oldContext);

			/* free any pallocs we made inside probeSegments() */
			MemoryContextReset(probeContext);

			/* Bump the version if configuration was updated. */
			if (updated_probe_state)
			{
				/*
				 * File GPSEGCONFIGDUMPFILE under $PGDATA is used by other
				 * components to fetch latest gp_segment_configuration outside
				 * of a transaction. FTS update this file in the first probe
				 * and every probe which updated gp_segment_configuration.
				 */
				StartTransactionCommand();
				writeGpSegConfigToFTSFiles();
				CommitTransactionCommand();

				ftsProbeInfo->status_version++;
			}
		}

		standbyInSync = (cdbs->entry_db_info[0].config->mode == GP_SEGMENT_CONFIGURATION_MODE_INSYNC);
		if (!am_masterprober && cdbs->total_entry_dbs == 2 && standbyInSync != standbyIsInSync())
		{
			ResourceOwner save = CurrentResourceOwner;

			standbyInSync = !standbyInSync;
			StartTransactionCommand();
			GetTransactionSnapshot();
			if (standbyInSync)
			{
				probeWalRepUpdateConfig(cdbs->entry_db_info[0].config->dbid, -1, 'p', true, true);
				probeWalRepUpdateConfig(cdbs->entry_db_info[1].config->dbid, -1, 'm', true, true);
			}
			else
			{
				probeWalRepUpdateConfig(cdbs->entry_db_info[0].config->dbid, -1, 'p', true, false);
				probeWalRepUpdateConfig(cdbs->entry_db_info[1].config->dbid, -1, 'm', false, false);
			}
			CommitTransactionCommand();
			CurrentResourceOwner = save;
		}

		/* Start the master prober if it's not started or the master and standby information has changed */
		if (gp_enable_master_autofailover &&
			!am_masterprober &&
			cdbs->total_entry_dbs == MAX_ENTRYDB_COUNT &&
			(!masterProberStarted || masterInfoChanged))
		{
			/* The primary/mirror segment of content 0 may have changed, get the up-to-date information */
			StartTransactionCommand();
			cdbs = readCdbComponentInfoAndUpdateStatus();
			CommitTransactionCommand();
			startMasterProber(cdbs, masterInfoChanged);
		}

		/* free current components info and free ip addr caches */	
		cdbcomponent_destroyCdbComponents();

		SIMPLE_FAULT_INJECTOR("ftsLoop_after_probe");

		/* Notify any waiting backends about probe cycle completion. */
		SpinLockAcquire(&ftsProbeInfo->lock);
		ftsProbeInfo->done_count = ftsProbeInfo->start_count;
		SpinLockRelease(&ftsProbeInfo->lock);


		/* check if we need to sleep before starting next iteration */
		elapsed = time(NULL) - probe_start_time;
		timeout = elapsed >= gp_fts_probe_interval ? 0 : 
							gp_fts_probe_interval - elapsed;

		/*
		 * In above code we might update gp_segment_configuration and then wal
		 * is generated. While synchronizing wal to standby, we need to wait on
		 * MyLatch also in SyncRepWaitForLSN(). The set latch introduced by
		 * outside fts probe trigger (e.g. gp_request_fts_probe_scan() or
		 * FtsNotifyProber()) might be consumed by it so we do not WaitLatch()
		 * here with a long timout here else we may block for that long
		 * timeout, so we recheck probe_requested here before waitLatch().
		 */
		if (probe_requested)
			timeout = 0;

		rc = WaitLatch(&MyProc->procLatch,
					   WL_LATCH_SET | WL_TIMEOUT | WL_POSTMASTER_DEATH,
					   timeout * 1000L);

		SIMPLE_FAULT_INJECTOR("ftsLoop_after_latch");

		ResetLatch(&MyProc->procLatch);

		/* emergency bailout if postmaster has died */
		if (rc & WL_POSTMASTER_DEATH)
			proc_exit(1);
	} /* end server loop */

	return;
}

/*
 * Check if FTS is active
 */
bool
FtsIsActive(void)
{
	return (!skipFtsProbe);
}

/*
 * Start master prober when 'startMasterProber' is set.
 */
bool
shouldStartMasterProber(void)
{
	return shmFtsControl->startMasterProber;
}
