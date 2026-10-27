# Q02 stale stage-1 claim repair

Recorded 2026-10-22T10:07:27.768834+00:00; maintenance run 1792663316.

Item: `lem-pur-system-evaluation-scalar-restriction-normalization`.

Q46's delivery b51d2975cf9 was accepted in commit 15c4d559cbd at
2026-10-22T08:32:22Z by reviewer NT-cc-Q46-b51d2975c. The live node is
`split` with `reviewed.result = pass`. Q02 acquired its claim at
2026-10-22T08:32:54Z, 32 seconds after that completion.

At repair time the live and shared queues contain no row for the item,
`dag_queue.stage1_completed(node)` is true, and no released repair note,
Q02 return entry, or Q02 delivery branch exists. The dispatcher kept
retrying the held claim with saved stage 1 after its queue row disappeared.
The worker's unchanged-item preflight failure and live-wins refusal are correct.

Released the stale Q02 claim with `tools/claim.py release`, retaining backups
of the claim and delivery log beside their original paths with suffix
`.maint-Q02-1792663316.bak`. Only this release line is staged from the delivery log;
pre-existing uncommitted log entries and other agents' changes are preserved.
The accepted DAG node, proof and review remain byte-identical.

Launcher follow-up (outside this repair's edit authority): in
`dispatch_all.py`, reconcile held stage-1 claims against live stage completion
when the queue no longer lists them; a missing queue stage currently leaves
`Group.server` using the saved stage, then `Group.work` starts another
worker. Keep released stage-1 repair orders actionable and keep failure counts
out of eligibility decisions. The queue-authority policy for listed items is
unchanged.

The next work on this item is stage 2 when its statement prerequisites make
it queue-ready, or stage 1 under a genuine released repair order. Do not
manufacture a split edit, attachment or repair order to pass the delivery gate.
No Lean was changed or compiled.

Release entry:
2026-10-22T10:07:27Z Q02 released lem-pur-system-evaluation-scalar-restriction-normalization: maintenance Q02/1792663316: stale stage-1 claim; Q46 split accepted at 15c4d559cbd, reviewer NT-cc-Q46-b51d2975c; live stage 1 completed, no queue row or released repair; release duplicate assignment
