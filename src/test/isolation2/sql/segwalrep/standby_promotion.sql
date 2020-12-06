-- This test is the master prober version of mirror_promotion
--
-- Tests standby promotion triggered by FTS in 2 different scenarios.
--
-- 1st: Shut-down of master and hence unavailability of master
-- leading to standby promotion. In this case the connection between
-- master and standby is disconnected prior to promotion and
-- walreceiver doesn't exist.
--
-- 2nd: Master is alive but using fault injector simulated to not
-- respond to fts. This helps to validate fts time-out logic for
-- probes. Plus also standby promotion triggered while connection
-- between master and standby is still alive and hence walreceiver
-- also exist during promotion.
--
-- This test assumes master port is 15432 and standby port is 16432

create extension if not exists gp_inject_fault;

include: helpers/server_helpers.sql;

-- set GUCs to speed-up the test
!\retcode gpconfig -c gp_fts_probe_retries -v 2;
!\retcode gpconfig -c gp_fts_probe_timeout -v 5;
!\retcode gpstop -u;

-- Test 1
-- cache session on seg0 where master prober on it
0U: select 1;

-- show the master information 
SELECT role, preferred_role, content, port, mode, status FROM gp_segment_configuration where content=-1;

-- stop master in order to trigger standby promotion
select pg_ctl((select datadir from gp_segment_configuration c
where c.role='p' and c.content=-1), 'stop');

-- trigger failover
0U: select gp_request_fts_probe_scan();

-- As master is down, standby has been promoted, connect to the new master 
1: \c 16432;
-- the preferred master is down
-- the preferred standby is master and it's up and not-in-sync
1: select content, preferred_role, role, status, mode
from gp_segment_configuration
where content = -1;

-- recover the preferred master as standby 
!\retcode MASTER_DATA_DIRECTORY=`psql -p 16432 postgres -At -c "select datadir from gp_segment_configuration where content=-1 and role='p'"` gprecoverseg -a -d `psql -p 16432 postgres -At -c "select datadir from gp_segment_configuration where content=-1 and role='p'"`;

-- loop while segments come in sync
1: do $$
begin /* in func */
  for i in 1..120 loop /* in func */
    if (select mode = 's' from gp_segment_configuration where content = 1 limit 1) then /* in func */
      return; /* in func */
    end if; /* in func */
    perform gp_request_fts_probe_scan(); /* in func */
  end loop; /* in func */
end; /* in func */
$$;

-- roles flipped and in sync
1: select content, preferred_role, role, status, mode from gp_segment_configuration where content = -1;

-- Test 2
-- inject fts handler to simulate fts probe timeout
1: select gp_inject_fault_infinite('fts_handle_message', 'infinite_loop', dbid)
from gp_segment_configuration
where content = -1 and role = 'p';

-- trigger failover
0U: show gp_fts_probe_retries;
0U: show gp_fts_probe_timeout;
0U: select gp_request_fts_probe_scan();

-- trigger one more probe right away which mostly results in sending
-- promotion request again to standby, while its going through
-- promotion, which is nice condition to test as well.
0U: select gp_request_fts_probe_scan();

-- start a new connection to port 15432
-- expect preferred master is up and standby is down
2: select content, preferred_role, role, status, mode
from gp_segment_configuration
where content = -1;

-- shutdown the standby
2: select pg_ctl((select datadir from gp_segment_configuration c
where c.role='m' and c.content=-1), 'stop');

-- recover the standby
!\retcode gprecoverseg -a;

-- master and standby are up and in-sync
2: select content, preferred_role, role, status, mode
from gp_segment_configuration
where content = -1;

-- set GUCs to speed-up the test
!\retcode gpconfig -r gp_fts_probe_retries;
!\retcode gpconfig -r gp_fts_probe_timeout;
!\retcode gpstop -u;
