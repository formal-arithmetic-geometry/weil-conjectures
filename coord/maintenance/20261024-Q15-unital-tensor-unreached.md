# Q15: retire an unreached stage-1 assignment

At 2026-10-24T08:13:02Z, audited the live repository under coord/.merge.lock. The item is
unsplit and NOT stage-1-complete. There is one DAG: queue_nodes_dir resolves to
this repository's dag/nodes. There is no side completion to promote.

Q96 introduced the item in 925158f4048. R6's accepted parent proof landing
806c3dd34c25ebffa0e1cfd2badf4658925cf834 removed every use/proof_deps edge from
lem-pur-dualizing-unit-composite to it. The current whole DAG has zero incoming
dependency edges to the item. It is absent from Dag.dist, Dag.dist1, stage1(),
the target list, and coord/queue.tsv, with no released repair note.

The returned packet 6026c4f0dd1e0bf0434ab018eb924692e45d079f was approved by the reader. nt_land_batch.py
places any item absent from stage1() in notopen, then incorrectly labels an
unsplit queue node as an unpromoted side completion. The resulting return
asks the worker to fix something outside its delivery. Repeated preflights
pass, including b488bd58f6f and 3fce847e894, without changing queue eligibility.

Archived the exact delivery at refs/superseded/Q15/lem-pur-unital-tensor-transport-cancellation/6026c4f0dd1e0bf0434ab018eb924692e45d079f; removed only its stale Q15 return;
released the stale Q15 claim with the maintenance reason above, without marking
it done or abandoned. This is withdrawal of an obsolete assignment, not completion
and not mathematical abandonment. The node, parent, Lean source, sandbox,
searches and citations are retained. Other Q15 returns remain byte-identical.

Backups before mutation: /home/ubuntu/weil-maint-bak/Q15-unital-tensor-20261024T081302Z/ (relative coord paths with .bak suffix,
plus delivery-ref.bak). The new record's backup records prior absence.
The commit uses a temporary index so other agents' uncommitted append-only
delivery-log records stay in the working tree and out of this maintenance commit.

Protected-tool follow-up (not edited in this task): nt_land_batch.py's notopen
diagnostic must distinguish absent target reach from completion, and compare
actual side/live records before claiming a promotion failure. The landing/
review owner should reconcile truly unreached stale packets instead of issuing
another mathematical repair. The dispatcher owner should reconcile returned
stage-1 assignments against live eligibility as well as ordinary new claims,
preserving released repairs and genuinely in-flight work. No failure cutoff,
concurrency cap, admission change, throttle or pause is called for.

Next worker: this assignment has left the live target route. Reuse the archived
approved split if a future dependency or released repair reaches it again; then
rebase, refresh citations and preflight. Do not invent a proof change, mark it
completed, or restore an unnecessary parent edge merely to satisfy dispatch.

Unchanged SHA-256 evidence:
- dag/nodes/sec-smooth-purity/lem-pur-unital-tensor-transport-cancellation.json: 92a9bb09e8a4264dc5b66f759ef46d93bc04e7dc0a4e4011c36c5ccacac59848
- dag/nodes/sec-smooth-purity/lem-pur-dualizing-unit-composite.json: e820740feff5becacf55094924bf9a5c98796a3b1ffabf80b9bc51b6fe822d28
- lean/Sheaf/Paper/DualizingUnitComposite.lean: a4c8afe952e25fb3e725f80d15e4eab6185fb951bf28410d8b13d7bd2e81fd09
