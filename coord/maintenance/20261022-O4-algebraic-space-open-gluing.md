# O4 obsolete stage-1 claim repair

Recorded 2026-10-22T10:07:44.918971+00:00 by pipeline maintenance.

Q147's accepted landing is 00f2af54fca9da1454e82bdd88c9acc2714d4a63
(2026-10-22T06:51:58Z), reviewer NT-cc-Q147-bb86d8894. The live
node dag/nodes/sec-trace-formula/lem-trf-algebraic-space-open-gluing.json is split, with review PASS.
The corresponding coord/repair-notes/lem-trf-algebraic-space-open-gluing.json is resolved at stage 1.
The two extracted nodes are lem-trf-open-sheaf-coproduct-base-change and
lem-trf-open-cover-representable-diagonal.

The stale coord/claims/lem-trf-algebraic-space-open-gluing.lock belonged to O4 since
2026-10-22T06:52:12Z, just after that landing. The current server queue has
no row for this item, and claim.node_finished(item, '1') is true. There is
no O4 delivery branch or open return for the item. The dispatcher retained
its old stage 1 when claim.queue_stage returned None and repeatedly launched
workers from the held claim. Its BLOCKED answers correctly obeyed the
live-wins rule in coord/brief-stage1.md; another split would be wrong.

Repair: backed up the claim and coord/deliveries.log, then used the normal
tools/claim.py release command under coord/.merge.lock. No abandonment was
recorded and the repair note was left resolved. The previous worker exited
naturally before release was requested. While the merge lock was awaited,
one final retry started at 10:07:14Z; it exited normally at 10:09:08Z.
No process was signalled. Backups:

- coord/claims/lem-trf-algebraic-space-open-gluing.lock.O4-maint-1792663251.bak
- coord/deliveries.log.O4-maint-1792663251.bak

No DAG statement, proof, Lean file, launcher code, review service or landing
tool changed. No compiler or Lake build ran. No concurrency or retry policy
changed.

Launcher-owner follow-up: dispatch_all.py Group.server/work must reconcile
held claims with the live queued stage and completion state. A missing queue
stage must not silently reuse an old stage-1 assignment. Release a completed
stage-1 claim when it has no released stage-1 repair, pending branch or open
return; preserve genuine unfinished work and explicit repair orders, and use
the current stage when the item advances. Recheck at worker start as needed
for the queue/landing race. Failure counts must remain counters only. This
launcher-owned file was not edited.

Next worker: this stage-1 repair is already accepted. Follow the two child
nodes' own assignments. Only an explicit newly released stage-1 repair can
reopen this parent. Its existing Lean sorry is not a request to repeat stage 1.

Verification at 2026-10-22T10:09:25Z: the dispatcher has no running or pending
worker for the item; its last entry is the normal worker-ended event at
10:09:08Z, with no stop event. The final retry counter is 45 and was not reset
or used as a dispatch restriction. Server checks show no claim or queue row,
completed stage 1, resolved repair, no O4 branch or open return. The live node
and repair note have no diff from accepted landing 00f2af54fca. The receipt
before this verification is preserved as this file plus .verification.bak.
