select role, preferred_role, mode, status from gp_segment_configuration where content=-1;

-- start_ignore
create or replace language plpythonu;
create or replace function run_gpinitstandby(host text, port text, datadir text, envport text)
returns text as $$
    import subprocess
    cmd = 'PGPORT=%s /home/gpadmin/workspace/gpdb.master/bin/gpinitstandby -s %s -P %s -F %s -a' % (envport, host, port, datadir)
    try:
        res = subprocess.check_output(cmd, stderr=subprocess.STDOUT, shell=True).replace('.', '')
    except subprocess.CalledProcessError as e:
        raise RuntimeError("command '{}' return with error (code {}): {}".format(e.cmd, e.returncode, e.output))
    return res
$$ language plpythonu;
select hostname as standby_host, port as standby_port, datadir as standby_datadir from gp_segment_configuration where content=-1 and preferred_role='m'; \gset
select port as master_port from gp_segment_configuration where content=-1 and preferred_role='p'; \gset
-- end_ignore

-- remove the current standby
-- start_ignore
\! gpinitstandby -ra
-- end_ignore
select role, preferred_role, mode, status from gp_segment_configuration where content=-1;

-- initialize a standby
-- start_ignore
select run_gpinitstandby(:'standby_host', :'standby_port', :'standby_datadir', :'master_port');
-- end_ignore
select gp_request_fts_probe_scan();
select role, preferred_role, mode, status from gp_segment_configuration where content=-1;
