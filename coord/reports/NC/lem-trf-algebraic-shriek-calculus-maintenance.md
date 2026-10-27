# Stage-1 stale-claim reconciliation

Item: `lem-trf-algebraic-shriek-calculus`; group NC; maintenance run NC-1792664411.

Q07's worker head `4eb1155e36a` was independently reviewed PASS by
`NT-cc-Q07-4eb1155e3` and accepted in commit
`cced0d848b98f8e95544e081c64828a6cf0e4383` at 2026-10-22T09:05:01Z.
The live item has six assembly steps and the landing added three statement nodes.
The stage-1 re-split repair note is resolved.

NC's claim was created at 2026-10-22T09:05:19Z, eighteen seconds after landing,
and subsequently tracked in build commit `e427a1d408d`. It outlived the item's
queue row. Both `dag_queue.stage1_completed` and `claim.node_finished(item, "1")`
return true, and `claim.queue_stage(item)` is None. There is no open NC or Q07
return and no NC delivery branch. NC's retained sandbox item equals the accepted
live node. Repeated required dry runs therefore correctly reject it with
"the item's node file is unchanged".

The dispatcher restarts held claims in `Group.work` without stage-1 completion
reconciliation (its held and pending paths), causing the repeated BLOCKED loop.
The dispatcher is protected from maintenance edits; its owner should reconcile
completed stage-1 held/pending work against current queue and explicit repair
obligations before relaunch. Preserve live queue authority and genuine repairs.
Do not use failure counts as eligibility, or introduce limits, delays, or pauses.

Maintenance used `tools/claim.py done NC` to close only the obsolete claim and
record completion with marker `maintenance NC-1792664411:`. This operation and
its commit ran under `SHEAF_LEAD=L-only flock coord/.merge.lock`. The commit
includes the claim deletion, that one delivery-log entry, and this report only.
Backups of the claim, log, repair note, and this report have suffix
`.maint-NC-1792664411.bak`. Unrelated working changes are preserved.

Next worker: there is no remaining stage-1 task on this item. Use Q07's accepted
split; do not manufacture node edits, repeat searches, or redo mathematics to
satisfy unchanged-file preflight. A genuine later reopening must supply a fresh
queue or return/repair obligation. The retained NC sandbox and old BLOCKED note
are historical evidence and do not supersede the accepted live completion.

No DAG or Lean source, sandbox, launcher file, retry counter, or dispatcher state
was changed. No compiler or Lake command was run, and no process was killed.
Accepted node SHA-256:
`401fae8114b92ec3b53de131a6a90ddeea5c9c8d45468ada96d590e485a66110`.
