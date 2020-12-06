-- This test is the master prober version of fts_unblock_primary, it tests
-- when standby is down and master will block all the following transactions
-- until master prober detects it and mark standby down.

-- This test assumes 3 primaries and 3 mirrors from a gpdemo segwalrep cluster
-- This test assumes master prober is running on segment 0 and dbid is 2

-- function to wait for standby to come up in sync (1 minute timeout)
create or replace function wait_for_streaming(contentid smallint)
returns void as $$
declare
  updated bool; /* in func */
begin /* in func */
  for i in 1 .. 120 loop /* in func */
    perform gp_request_fts_probe_scan(); /* in func */
    select (mode = 's' and status = 'u') into updated /* in func */
    from gp_segment_configuration /* in func */
    where content = contentid and role = 'm'; /* in func */
    exit when updated; /* in func */
    perform pg_sleep(0.5); /* in func */
  end loop; /* in func */
end; /* in func */
$$ language plpgsql;

include: helpers/server_helpers.sql;

-- make sure we are in-sync for the master we will be testing with
select sync_state from pg_stat_replication;
-- gp_segment_configuration on segment 0 shows master/standby is in-sync
0U: select content, role, preferred_role, mode, status from gp_segment_configuration;

-- synchronous_standby_names should be set to '*' by default on master, since
-- we have a working/sync'd standby
show synchronous_standby_names;
show gp_fts_mark_mirror_down_grace_period;

-- create table and show commits are not blocked
create table fts_unblock_master (a int) distributed by (a);

-- skip master prober probes always
create extension if not exists gp_inject_fault;
select gp_inject_fault('fts_probe', 'reset', 2);
select gp_inject_fault_infinite('fts_probe', 'skip', 2);
-- force scan to trigger the fault
0U: select gp_request_fts_probe_scan();
-- verify the failure should be triggered once
select gp_wait_until_triggered_fault('fts_probe', 1, 2);

-- stop the standby
-1U: select pg_ctl((select datadir from gp_segment_configuration c where c.role='m' and c.content=-1), 'stop');

-- this should block since standby is not up and sync replication is on
2: begin;
2: insert into fts_unblock_master values (4);
2&: commit;

-- resume master prober probes
select gp_inject_fault('fts_probe', 'reset', 2);

-- trigger fts probe and check to see master marked n/u and standby still n/u as
-- still should be in standby down grace period.
0U: select gp_request_fts_probe_scan();
0U: select content, role, preferred_role, mode, status from gp_segment_configuration where content=-1;

-- set standby down grace period to zero to instantly mark standby down
!\retcode gpconfig -c gp_fts_mark_mirror_down_grace_period -v 0;
!\retcode gpstop -u;

-1U: show gp_fts_mark_mirror_down_grace_period;

-- trigger fts probe and check to see master marked n/u and standby n/d
0U: select gp_request_fts_probe_scan();
0U: select content, role, preferred_role, mode, status from gp_segment_configuration where content=-1;

-- should unblock and commit after FTS sent standby a SyncRepOff libpq message
2<:

-- synchronous_standby_names should now be empty on master
-1U: show synchronous_standby_names;

--hold walsender in startup
select gp_inject_fault_infinite('initialize_wal_sender', 'suspend', dbid)
    from gp_segment_configuration where role='p' and content=-1;

-- bring the standby back up and see master s/u and standby s/u
-1U: select pg_ctl_start(c.datadir, c.port, c.content, c.dbid) from gp_segment_configuration c where c.role='m' and c.content=-1;
select gp_wait_until_triggered_fault('initialize_wal_sender', 1, dbid)
    from gp_segment_configuration where role='p' and content=-1;
-- make sure the walsender on master is in startup
select state from gp_stat_replication where gp_segment_id=-1;
0U: select gp_request_fts_probe_scan();
-- standby should continue to be reported as down since walsender is in startup
0U: select content, role, preferred_role, mode, status from gp_segment_configuration where content=-1;

-- let the walsender proceed
select gp_inject_fault('initialize_wal_sender', 'reset', dbid)
    from gp_segment_configuration where role='p' and content=-1;
select wait_for_streaming(-1::smallint);
0U: select gp_request_fts_probe_scan();
0U: select content, role, preferred_role, mode, status from gp_segment_configuration where content=-1;

-- everything is back to normal
insert into fts_unblock_master select i from generate_series(1,10)i;

-- synchronous_standby_names should be back to its original value on master
-1U: show synchronous_standby_names;

!\retcode gpconfig -r gp_fts_mark_mirror_down_grace_period;
!\retcode gpstop -u;
-1U: show gp_fts_mark_mirror_down_grace_period;
