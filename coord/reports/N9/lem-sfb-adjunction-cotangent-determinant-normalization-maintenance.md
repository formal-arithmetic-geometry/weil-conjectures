# Stale stage-1 assignment repaired (N9, 2026-10-22)

Item: `lem-sfb-adjunction-cotangent-determinant-normalization`.

Q02's split was accepted in commit
`370a71a64356b9ed18ca983f93e7f918cb13e6c7`, reviewed by
`NT-cc-Q02-9381b279a`. `coord/deliveries.log` records completion at
2026-10-22T04:57:28Z. N9 acquired the duplicate claim at
2026-10-22T04:58:03Z, 35 seconds after completion. Its retained dispatcher
stage was 1 even after the queue stopped listing the item. The node is split,
reviewed/pass, and has no Lean record. There is no N9 return, delivery branch,
or released repair note for this assignment.

The worker correctly preserved the accepted node; stage-1 delivery preflight
correctly rejected the identical copy with "the item's node file is unchanged".
The dispatcher repeatedly treated the held stale claim as new stage-1 work.
This was stale assignment bookkeeping, with no mathematical repair needed.

Under `coord/.merge.lock`, backed up the original claim and deliveries log and
ran `tools/claim.py release N9 <item>` with a maintenance explanation. This is
an ordinary release, not an abandonment or a parked stage-2 item. Verified
that the claim is gone, the queue still has no row for the item, and the
accepted node is byte-for-byte unchanged. All failure history is retained.
No dispatch limit, waiting rule, or concurrency setting was introduced.

Backups:
- `coord/claims/lem-sfb-adjunction-cotangent-determinant-normalization.lock.maint-N9-1792646928.bak`
- `coord/deliveries.log.maint-N9-1792646928.bak`


The launcher-owned dispatcher is outside this repair's editable scope. Its
held-claim path should reconcile a missing queue row against authoritative
completion for the stored stage, and release a completed assignment after
checking for an open return or repair. Absence from the queue alone does not
establish completion; a missing stage-2 row must not be interpreted as a
completed stage-2 statement. Queued work continues to be dispatched under the
human's standing rule. The launcher-side maintenance REPORT.md records the
specific source locations requiring review; no launcher code was changed.

Next worker: stage 1 is complete. Preserve Q02's nine-step accepted split and
its review. Do not manufacture a node edit to pass the unchanged-file gate,
repeat identical dry runs, or push a duplicate delivery. A future stage-2
assignment must come from the normal stage-2 queue or an explicit repair.
