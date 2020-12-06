import sys
import signal
from gppylib.gparray import GpArray
from gppylib.db import dbconn
from gppylib.commands.gp import GpSegStopCmd
from gppylib.commands import base
from gppylib import gplog

from gppylib.operations.segment_reconfigurer import SegmentReconfigurer, MasterReconfigurer

MIRROR_PROMOTION_TIMEOUT=30


class ReconfigDetectionSQLQueryCommand(base.SQLCommand):
    """A distributed query that will cause the system to detect
    the reconfiguration of the system"""

    query = "SELECT * FROM gp_dist_random('gp_id')"

    def __init__(self, conn):
        base.SQLCommand.__init__(self, "Reconfig detection sql query")
        self.cancel_conn = conn

    def run(self):
        dbconn.execSQL(self.cancel_conn, self.query)


class GpSegmentRebalanceOperation:
    def __init__(self, gpEnv, gpArray):
        self.gpEnv = gpEnv
        self.gpArray = gpArray
        self.logger = gplog.get_default_logger()

    def rebalance(self):
        # Get the unbalanced primary segments grouped by hostname
        # These segments are what we will shutdown.
        self.logger.info("Getting unbalanced segments")
        unbalanced_primary_segs = GpArray.getSegmentsByHostName(self.gpArray.get_unbalanced_primary_segdbs())
        pool = base.WorkerPool()

        try:
            # Disable ctrl-c
            signal.signal(signal.SIGINT, signal.SIG_IGN)

            self.logger.info("Stopping unbalanced primary segments...")
            for hostname in unbalanced_primary_segs.keys():
                cmd = GpSegStopCmd("stop unbalanced primary segs",
                                   self.gpEnv.getGpHome(),
                                   self.gpEnv.getGpVersion(),
                                   'fast',
                                   unbalanced_primary_segs[hostname],
                                   ctxt=base.REMOTE,
                                   remoteHost=hostname,
                                   timeout=600)
                pool.addCommand(cmd)

            base.join_and_indicate_progress(pool)
            
            failed_count = 0
            completed = pool.getCompletedItems()
            for res in completed:
                if not res.get_results().wasSuccessful():
                    failed_count += 1

            allSegmentsStopped = (failed_count == 0)

            if not allSegmentsStopped:
                self.logger.warn("%d segments failed to stop.  A full rebalance of the")
                self.logger.warn("system is not possible at this time.  Please check the")
                self.logger.warn("log files, correct the problem, and run gprecoverseg -r")
                self.logger.warn("again.")
                self.logger.info("gprecoverseg will continue with a partial rebalance.")

            pool.empty_completed_items()
            segment_reconfigurer = SegmentReconfigurer(logger=self.logger,
                    worker_pool=pool, timeout=MIRROR_PROMOTION_TIMEOUT)
            segment_reconfigurer.reconfigure()

            # Final step is to issue a recoverseg operation to resync segments
            self.logger.info("Starting segment synchronization")
            original_sys_args = sys.argv[:]
            try:
                self.logger.info("=============================START ANOTHER RECOVER=========================================")
                # import here because GpRecoverSegmentProgram and GpSegmentRebalanceOperation have a circular dependency
                from gppylib.programs.clsRecoverSegment import GpRecoverSegmentProgram
                sys.argv = ['gprecoverseg', '-a']
                local_parser = GpRecoverSegmentProgram.createParser()
                local_options, args = local_parser.parse_args()
                cmd = GpRecoverSegmentProgram.createProgram(local_options, args)
                cmd.run()

            except SystemExit as e:
                if e.code != 0:
                    self.logger.error("Failed to start the synchronization step of the segment rebalance.")
                    self.logger.error("Check the gprecoverseg log file, correct any problems, and re-run")
                    self.logger.error("'gprecoverseg -a'.")
                    raise Exception("Error synchronizing.\nError: %s" % str(e))
            finally:
                if cmd:
                    cmd.cleanup()
                sys.argv = original_sys_args
                self.logger.info("==============================END ANOTHER RECOVER==========================================")

        except Exception, ex:
            raise ex
        finally:
            pool.join()
            pool.haltWork()
            pool.joinWorkers()
            signal.signal(signal.SIGINT, signal.default_int_handler)

        return allSegmentsStopped # if all segments stopped, then a full rebalance was done

    def rebalanceMaster(self):
        try:
            # Disable ctrl-c
            signal.signal(signal.SIGINT, signal.SIG_IGN)

            # Stop the master
            self.logger.info("Stopping the master...")
            stopcmd = GpSegStopCmd("stop master",
                               self.gpEnv.getGpHome(),
                               self.gpEnv.getGpVersion(),
                               'fast',
                               [self.gpArray.master],
                               ctxt=base.REMOTE,
                               remoteHost=self.gpArray.master.getSegmentHostName(),
                               timeout=MIRROR_PROMOTION_TIMEOUT)
            stopcmd.run()
            res = stopcmd.get_results()
            if res is None or not res.wasSuccessful():
                raise Exception("Failed to stop the master")
            self.logger.info("Master is stopped")

            # Trigger master prober to bring the standby back
            master_reconfigurer = MasterReconfigurer(self.logger, self.gpArray, MIRROR_PROMOTION_TIMEOUT)
            master_reconfigurer.reconfigure()

            # Final step is to issue a recoverseg operation to resync segments
            self.logger.info("Starting master synchronization")
            original_sys_args = sys.argv[:]
            cmd = None
            try:
                self.logger.info(
                    "=============================START ANOTHER RECOVER=========================================")
                # import here because GpRecoverSegmentProgram and GpSegmentRebalanceOperation have a circular dependency
                from gppylib.programs.clsRecoverSegment import GpRecoverSegmentProgram
                sys.argv = ['gprecoverseg', '-d', self.gpArray.standbyMaster.getSegmentDataDirectory(), '-a']
                local_parser = GpRecoverSegmentProgram.createParser()
                local_options, args = local_parser.parse_args()
                cmd = GpRecoverSegmentProgram.createProgram(local_options, args)
                cmd.run()

            except SystemExit as e:
                if e.code != 0:
                    self.logger.error("Failed to start the synchronization step of the master rebalance.")
                    self.logger.error("Check the gprecoverseg log file, correct any problems, and re-run")
                    self.logger.error("'gprecoverseg -a -d %s'." % self.gpArray.standbyMaster.getSegmentDataDirectory())
                    raise Exception("Error synchronizing.\nError: %s" % str(e))
            finally:
                if cmd:
                    cmd.cleanup()
                sys.argv = original_sys_args
                self.logger.info(
                    "==============================END ANOTHER RECOVER==========================================")
        except Exception, ex:
            raise ex
        finally:
            signal.signal(signal.SIGINT, signal.default_int_handler)

