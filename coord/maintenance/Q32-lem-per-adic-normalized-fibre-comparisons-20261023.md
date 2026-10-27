# Q32 maintenance: stale completed stage-1 claim

Item: `lem-per-adic-normalized-fibre-comparisons`.

NU's four-node re-split was accepted in `4dac4c5276c` at 2026-10-22
11:23:41 UTC (reviewer `NT-cc-NU-40b056da6`). Q32 acquired its claim at
11:25:55 UTC. The live node has status `split` and a passing stage-1 review;
its stage-2 Lean record also passed. Its stage-1 repair note is `resolved`.
At maintenance the item has no row in `coord/queue.tsv`, no Q32 delivery
branch and no open Q32 return.

The dispatcher continues to schedule held claims after they leave the queue.
`Group.server()` leaves the cached stage unchanged when `claim.queue_stage()`
returns None; `Group.work()` has completion reconciliation only for stage 3.
It therefore keeps starting stage-1 workers on the accepted split. Each worker
correctly retains the live split; dry-run preflight then correctly rejects the
unchanged item. This is stale assignment data, not a mathematical or preflight
failure. Launcher-owned dispatcher code is outside this maintenance's edit scope.

Repair: backed up the Q32 claim and deliveries log, then released only this
completed off-queue claim with `tools/claim.py release Q32`. No abandonment,
parking, failure-count limit, queue suppression or concurrency change was used.
The accepted node, module, repair note and queue are unchanged. The worker's
sandbox was separately retained as `worker-sandbox.bak` in the maintenance
working directory on the launcher machine.

Server backups: `coord/maintenance/backups/Q32-lem-per-adic-normalized-fibre-comparisons-20261023/`.

Validation: live stage-1 and stage-2 completion predicates are true, the repair
state is resolved, the Q32 claim is absent, and the accepted node and repair
record retain their original SHA-256 hashes. No Lean source changed, so no
compiler or Lake invocation was needed.

Next worker: follow current queue membership and any new released repair order.
Do not redo NU's accepted split or change metadata to evade the unchanged-file
gate. The unfinished Lean proof is separate stage-3 work and is not this task.
The launcher REPORT.md describes the proposed dispatcher reconciliation.
