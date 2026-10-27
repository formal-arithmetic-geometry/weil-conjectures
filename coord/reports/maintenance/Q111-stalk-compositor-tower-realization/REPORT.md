# Q111 stale stage-1 claim repair

Date: 2026-10-22T09:16:32Z
Item: `lem-trf-stalk-compositor-tower-realization`. Dispatcher key: `lem-trf-stalk-compositor-tower-realization@new`.

Cause: Q07's delivery e6576f84d46 was accepted as commit
0dd5e69b2f395689f6bb728ade090cb27b3aca9a at 2026-10-22T07:53:27Z,
with independent passing review by NT-cc-Q07-e6576f84d. Q111's claim
was created at 07:53:46Z (19 seconds later), and its first worker started
at 07:54:20Z. The retained sandbox is an exact copy of the accepted node.
The delivery preflight correctly rejects it as an unchanged item.
There is no stage-1 repair note, Q111 return, or Q111 delivery branch.

The live queue no longer lists the item (`claim.queue_stage` is None).
`claim.node_finished(item, '1')` is True. The dispatcher server() leaves
its cached stage unchanged when the queue has no row; work() restarts
held stage-1 claims without checking completion. Its stage-3 path has
completion checks. Repeated BLOCKED answers therefore restart the same
obsolete claim. Failure counts are symptoms, not the cause.

Repair: backed up and released only the obsolete Q111 claim through
`tools/claim.py release`, and recorded the release in coord/deliveries.log
and coord/ledger.md. No node, proof, Lean file, review, queue, launcher
code, failure count, limit or pause was changed. No process was killed.

Backups of the deleted claim and the pre-edit journal files are in
`local/maintenance/Q111-stalk-compositor-tower-realization-1792660404/` with .bak suffixes.
Node SHA-256 before and after: `0d7ad26572ddec3957c76bb6dc700260d5b1b66b228715fb33580512f425942a`.

Launcher follow-up (protected file, deliberately not edited):
`/home/ubuntu/weil-launcher-all/dispatch_all.py`, Group.server/Group.work,
should reconcile a held claim with current stage/completion when the
server queue no longer lists it. Release an obsolete completed stage-1
claim through the claim tool after checking current node and released
repair-note state. Preserve actionable repairs and follow the human's
rule that queued unclaimed work is dispatched; use no failure threshold,
backoff, throttle, cap, admission restriction or pause. Do not weaken
the delivery preflight or fabricate a node change to satisfy it.

Next worker: stage 1 is already accepted. Do not resplit or re-deliver
it without an explicit released stage-1 repair note. A future stage-2
assignment is separate: stage-1 completion does not claim a Lean proof.
The earlier worker sandbox and report were left intact.

Verification before release: accepted status/review, no queue row, no
released repair, no Q111 return/branch, current Q111 claim ownership.
Verification after release: claim absent and accepted node hash unchanged.
No Lean compilation is needed for this coordination-only repair.
