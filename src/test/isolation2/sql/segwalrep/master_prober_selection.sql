-- Tests master prober selection
--
-- When the master prober segment is down, master will
-- start another master prober on another segment if
-- master and standby are in-sync.
--

include: helpers/server_helpers.sql;

create extension if not exists gp_inject_fault;

-- stop primary segment 0
select pg_ctl(datadir, 'stop') from gp_segment_configuration where content = 0 and role = 'p';
-- trigger manual probe
select gp_request_fts_probe_scan();
-- mirror segment 0 will be promoted
select role, preferred_role from gp_segment_configuration where content = 0;
-- wait until master prober is started
do $$
begin /* in func */
  for i in 1..120 loop /* in func */
    begin
      if (select gp_request_fts_probe_scan() from gp_dist_random('gp_id') where gp_segment_id = 0) then /* in func */
        return; /* in func */
      end if; /* in func */
    exception when others then /* in func */
    end; /*in func */
    perform gp_request_fts_probe_scan(); /* in func */
  end loop; /* in func */
end; /* in func */
$$;
-- stop standby
select pg_ctl(datadir, 'stop') from gp_segment_configuration where content=-1 and role='m';
-- master transaction should be blocked 
1: begin;
1&: end;
-- verify the master prober can still work
0U: select gp_request_fts_probe_scan();
1<:

-- start standby
select pg_ctl_start(datadir, port, content, dbid) from gp_segment_configuration where content=-1 and role='m';
-- wait standby is in-sync
do $$
begin /* in func */
  for i in 1..120 loop /* in func */
    if (select sync_state='sync' from pg_stat_replication) then /* in func */
      return; /* in func */
    end if; /* in func */
    perform gp_request_fts_probe_scan(); /* in func */
  end loop; /* in func */
end; /* in func */
$$;
-- and trigger manual probe 
select gp_request_fts_probe_scan();

-- recover and rebalance segment 0 
!\retcode gprecoverseg -a;
!\retcode gprecoverseg -r;
select role, preferred_role from gp_segment_configuration where content = 0;

-- master prober is started on the primary segment 
0U: select gp_request_fts_probe_scan();
