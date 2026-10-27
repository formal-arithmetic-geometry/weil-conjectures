# Q46 flat-model stale stage-1 claim reconciliation

Reconciled at 2026-10-23T04:09:10.023985+00:00.

NR's accepted stage-1 re-split of `sk-lem-sf-flat-model` is commit `610a3468f0a`,
reviewed by `NT-cc-NR-5e1eebaaf` with result PASS. The ledger records the
06:18 UTC merge on 2026-10-22 with two extracted argument nodes, and
coord/deliveries.log records completion at 06:18:44 UTC. Its repair note
is resolved. Q46 acquired the claim at 06:19:34 UTC, after this accepted
landing. The queue later dropped the completed item, but its claim remained.
The configured claim TTL is 259200 seconds (72 hours), so it was
still active at this maintenance check, not expired.

Cause: a stale queue/claim race followed by the protected launcher's held
claim fallback. `Group.server()` in dispatch_all.py gets queue stage `-`
and retains saved stage `1`; `Group.work()` then treats the held claim as
new work, without checking live stage-1 completion. The take path honors
the human's listed-item dispatch rule. The repeated BLOCKED answers are
correct applications of the live-wins rule and delivery-errors A7: another
split or delivery is forbidden after NR's accepted repair. This is not a
mathematical defect or an unresolved repair. The maintenance trigger counted
89 failures; those counts were not used to stop eligible work.

Under `SHEAF_LEAD=L-only flock coord/.merge.lock`, rechecked the exact
claim owner and timestamp, passing review, resolved repair, live stage-1
and stage-2 completion predicates, no queue row, no Q46 return and no
outstanding delivery for this item. Backed up the claim and deliveries log,
then ran `tools/claim.py release Q46 sk-lem-sf-flat-model` with the explicit
reconciliation reason. Only that obsolete assignment was released.

Validation: claim absent, not held by Q46, still off queue; an actual
stage-aware take refused with `sk-lem-sf-flat-model is already completed for stage 1 (live node); nothing to claim for that stage`. The accepted node, module and
repair record retain these SHA-256 values:

- `dag/nodes/sec-six-functors-basics/sk-lem-sf-flat-model.json`: `4756ad39241a9c172240aedc4778912318a24668ad8b95d53000823fc9627e13`
- `coord/repair-notes/sk-lem-sf-flat-model.json`: `5f2c34b14d32de538cb03b00fd8b158f175fae9f57530caf2fc04bb535289154`
- `lean/Sheaf/SixFunctors/FlatModel.lean`: `00a8370ca50a6ad054d4cfc1cdfcca08e2ede5a24109febca49eed8997e6be80`

Changed paths:

- `coord/claims/sk-lem-sf-flat-model.lock`: obsolete claim deleted.
- `coord/deliveries.log`: normal claim.py release record appended.
- `coord/maintenance/20261023-Q46-flat-model-stale-claim.md`: this maintenance record.

Backups on the server, intentionally not staged:

- `coord/claims/sk-lem-sf-flat-model.lock.maint-Q46-1792728217.bak`
- `coord/deliveries.log.maint-Q46-1792728217.bak`
- `coord/maintenance/20261023-Q46-flat-model-stale-claim.md.bak`: snapshot of the new maintenance record.

No DAG, Lean, brief, worker sandbox or launcher implementation was changed.
No Lean compilation or lake build was needed for this coordination repair.
No worker process was killed, and no cap, throttle, admission limit, pause
or failure-count gate was introduced.

Protected launcher follow-up (report only): reconcile a held stage-1 claim
when a successful authoritative read establishes no current queue row,
completed live stage 1, and no open return, pending delivery or released
stage-1 repair. Do not keep dispatching it with a remembered stage after
queue_stage returns None. Carry the requested stage through claim/start and
refresh it from current queue rows. Preserve the human's rule that listed
unclaimed work is dispatched, plus explicit returns and released repairs;
a failed/empty read alone is not evidence of completion. The maintenance
brief forbids editing dispatch_all.py, so no launcher patch was made here.

Next worker: stage 1 is already accepted at `610a3468f0a`. Preserve NR's
split and its two extracted dependencies. There is no replacement split,
ATTACH or report-only delivery due. Follow the live queue and current repair
state; a future stage-2 or stage-3 task is separate. The existing Lean record
and completion predicates are workflow records, not a new proof certificate.
Keep the historical Q46 sandbox and the 89-attempt diagnostic history.
