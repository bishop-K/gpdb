-- start_ignore
! gpconfig -c gp_enable_master_autofailover -v on; 
! gpstop -rai;
-- end_ignore
0U: do $$
begin /* in func */
  for i in 1..10 loop /* in func */
    if (select count(*)=2 from gp_segment_configuration) then /* in func */
      return; /* in func */
    end if; /* in func */
    perform pg_sleep(1); /* in func */
  end loop; /* in func */
end; /* in func */
$$;
0U: select content, dbid, mode, status, role, preferred_role from gp_segment_configuration;
