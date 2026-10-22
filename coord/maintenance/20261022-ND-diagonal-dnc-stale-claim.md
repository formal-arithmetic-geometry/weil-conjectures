# ND diagonal DNC stale claim reconciliation (2026-10-22)

NO's stage-2 delivery was reviewed PASS by NT-stage2-cc-4c7b8ada1 and landed
at commit 3ccb45d31711f7e40cd71bb6ea3ba6d82baa0d7d, at 02:15:57 UTC.
6e50b3ec12cd43dea3aac0a10f2becc1 is the batch identifier, not a Git commit.
ND claimed the item at 02:16:15 UTC while queue data still allowed it.
The live queue subsequently removed the item, but ND's held claim survived.
The dispatcher retained stage 2 when Group.server reported queue stage '-';
Group.work then repeatedly started it as new work without checking completion.
Every worker correctly refused to re-push the already landed statement under
coord/brief-stage2.md section 2. This is stale bookkeeping, not mathematics.

Under coord/.merge.lock with SHEAF_LEAD=L-only, backed up the claim and
coord/deliveries.log, then closed only ND's stale claim via tools/claim.py done.
Verified: node_finished(item, '2') is true, queue_stage is None, reviewed_lean
is PASS for NO, no delivery branch, no open ND/NO return, and no repair note.
The node and Lean module hashes were identical before and after reconciliation.
No Lean source, brief, launcher tool, review service, or landing tool changed.
The next worker should use the landed declaration and not re-deliver this item
unless an explicit new repair request appears. Stage-3 proof work is unaffected.

Backups (preserved on the server):
- coord/claims/lem-pur-diagonal-dnc-chart-normalization.lock.maint-ND-1792636234.bak
- coord/deliveries.log.maint-ND-1792636234.bak

Launcher follow-up (report only; dispatch_all.py is outside editable scope):
reconcile held stage-1/2 claims against live completion when they have left the
live queue. Preserve delivery branches, open returns, and released repair notes;
preserve the human's rule that a listed, unclaimed item must be dispatched.
Do not add failure-count gates, caps, throttles, admission limits, waits or pauses.
