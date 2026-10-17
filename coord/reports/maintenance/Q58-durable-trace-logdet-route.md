# Q58 durable trace/logarithmic-determinant route repair

Ten consecutive Q58 prop-every-iterate-trace stage-1 attempts failed server
preflight because sk-thm-trace-transport could not reach sk-prop-logdet after
the retained worker split removed a circular determinant dependency.

Q05 maintenance commit 5bbd1b41ba already repaired the Euler-product node's
Steps 1 and 5 and its dependency/tool records. Sync commit 7486c8f434 then
replaced that side-only repair with the authoritative live DAG's old record.
The live record and the newtargets record both still exactly matched the
preimage of 5bbd1b41ba when this repair was prepared.

Reinstall that exact corrected record in the authoritative live DAG first,
then in newtargets, under each project's merge lock. No new mathematics or
new node: use the existing closed pure linear-algebra identity over E and
the blueprint's existing lem-zl-euler-product-identity over Qbar. Remove the
dependency on the whole geometric prop-trace-determinant statement, which
also depends on prop-every-iterate-trace. Keep the statements and unit routes.

The server audit with the retained Q58 overlay removes the reported unit
finding, introduces no unit findings or cycles, and passes review_split for
the repaired Euler-product node and the Q58 item. The normal delivery dry
run remains the final check; see the maintenance run REPORT.md and logs.

Next worker: preserve the existing sandbox and run the normal no-push dry
run on the fresh base, then proceed to the independent reader if accepted.
Do not restore the circular determinant input or add an unused dependency.
No launcher, landing, review-service, sync-tool or Lean source is changed.
Backups of all edited files use .maint-Q58-1792208862.bak.
