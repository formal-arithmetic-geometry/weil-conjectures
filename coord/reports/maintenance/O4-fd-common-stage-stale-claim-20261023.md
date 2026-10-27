# O4 common-stage comparison descent: stale claim reconciled

At 2026-10-22T19:24:45.287388+00:00, maintenance released O4's obsolete stage-1 claim through
`tools/claim.py release`. No mathematics or Lean source changed.

Q11's reviewed delivery 5b87889d045 landed in
`8bc94dfda64eb2ee38b0af5d509922222d0ffea6` at 2026-10-22T11:05:05Z
(deliveries.log; commit timestamp 11:05:06Z). It supplied the three statement-only
helpers lem-fd-hom-linear-equivalence, lem-fd-shift-triangle-reflection and
lem-fd-mixed-pullback-transformation. The live node is split and reviewed PASS by
NT-cc-Q11-5b87889d0; its stage-1 repair note is resolved. Both
`dag_queue.stage1_completed(node)` and `claim.node_finished(item, "1")` are true.

O4's claim began at 2026-10-22T11:05:26Z, 21 seconds after the recorded landing.
The item subsequently disappeared from queue.tsv, queue-batches.tsv and
queue-batches-all.tsv. There is no O4 return entry or delivery branch for it.
The dispatcher retains its cached stage when queue_stage returns None and its
held-claim work path does not reconcile stage-1 completion. This repeatedly
assigned already accepted work; the unchanged-node preflight rejection is correct.

The protected launcher dispatch_all.py was not edited. Its owner should reconcile
already-held stage-1 claims against live completion when no queue row, active
repair, return or delivery remains. Preserve the human's rule that listed,
unclaimed tasks dispatch and that failure counts never stop valid work.

The release and this audit's commit run under SHEAF_LEAD=L-only and
coord/.merge.lock, with Git identity Bin Wu <844524296@qq.com>. A temporary Git
index includes only this claim deletion, its release log line and this audit;
unrelated staged and working-tree changes are preserved.

Backups before mutation:
- coord/claims/lem-fd-common-stage-comparison-descent.lock.O4-maint-1792696949.bak
- coord/deliveries.log.O4-maint-1792696949.bak
- coord/reports/maintenance/O4-fd-common-stage-stale-claim-20261023.md.bak (initial audit checkpoint)

Protected content SHA-256 before and after reconciliation:
- dag/nodes/sec-fourier-transform/lem-fd-common-stage-comparison-descent.json: 9f3d712d78535f71d42f88418abb35327848b8aa86c64dd3a1bfb406c02dc701
- coord/repair-notes/lem-fd-common-stage-comparison-descent.json: 33689661dc88fb8f1bcbac8ed87845043281d0953001ec890dea6459b5dcae71
- lean/Sheaf/Paper/FdCommonStageComparisonDescent.lean: c30a8cfdedb807d44dde07a9f23efe9247b3c884d9b42e73f7f67f00d56fb6ad

Next worker: this parent has no outstanding stage-1 repair. Preserve Q11's reviewed
split and its three existing helpers. Do not alter or redeliver the parent to
satisfy the unchanged-item gate. Work from the current queue and any future
explicitly released repair. The old O4 sandbox report is historical evidence.
Existing stage-2 metadata does not claim a sorry-free proof. No Lean compilation
is required for this bookkeeping-only repair; no Lake build or process kill ran.
