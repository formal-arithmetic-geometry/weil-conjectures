# Q07 maintenance: completed stage-1 assignment retained by a stale claim

## Cause and evidence

Q95's reviewed three-node re-split landed at server commit `9492e6b729b`
(`2026-10-22T10:58:52Z` in coord/deliveries.log). It resolved the released
stage-1 repair and replaced the 5321-character proof by a 1251-character assembly.
The live node is `split`, independently reviewed `pass` by
`NT-cc-Q95-2fea18799`; the repair note is `resolved`.

Q07 obtained a fresh claim at `2026-10-22T10:58:57Z`, five seconds after that
landing, while the launcher's stage-1 queue view still included the item.
The claim record has `who=Q07`, `t=1792666737.0959227`. The current server
coord/queue.tsv, queue.md, queue-batches.tsv and queue-batches-all.tsv have no
row for this DAG id. There is no delivery branch or open return for this item
under Q07. Neither a new repair nor unfinished mathematics authorized another
stage-1 split.

dispatch_all.py Group.server() leaves the saved stage unchanged when
claim.queue_stage() returns None. Group.work() keeps restarting held stage-1
claims without reconciling completed, off-queue items. Every retained Q07
last.txt reports the same unchanged-item preflight failure; the dispatcher
state counted 14 failures after its first five BLOCKED retries. The retained
sandbox node is byte-identical to live (SHA256
2fe0c88f358f3d34ad68db36660606796c5bee042be00c4c0b070c868bc6df4f).
The preflight gate is correct. This is a stale assignment, not a proof defect,
compiler failure, permission problem or provider failure.

## Repair

Under SHEAF_LEAD=L-only and coord/.merge.lock, backed up the claim and
coord/deliveries.log with suffix `.maint-Q07-1792697387.bak`, then used
`python3 tools/claim.py release Q07 <item> <maintenance reason>` to release
only this superseded claim. The tool removed the claim and appended the audit
entry to coord/deliveries.log. This report is new. The node, repair note,
Lean module, worker sandbox, launcher state and protected tools were not edited.

Before release, assertions rechecked Q95's passing review, the resolved
stage-1 repair, queue absence, Q07 ownership, no Q07 return and no delivery
branch. After release, assertions verified the claim is absent, Q07 no longer
holds the item, the queue has no row, and node/repair bytes are unchanged.
No Lean source changed, so no compiler or Lake command was needed.

## Next worker and launcher follow-up

There is no remaining stage-1 assignment on this item. Preserve Q95's reviewed
split and its three child nodes. A future released stage-1 repair can reopen it
through normal claims; a stage-3 assignment on
Sheaf.Paper.PurShiftedTateUnitScalarCoherence is separate work. This release
does not claim the Lean theorem is proved.

The launcher-owned dispatch_all.py must be changed by its owner: reconcile
held stage-1 claims before generating pending/new work when the authoritative
server queue no longer lists the assignment. Release a claim only after
confirming stage-1 completion, no released stage-1 repair, and no outstanding
return/delivery. Keep listed items dispatchable as the human requires, and
retain failure counts. Do not change preflight, add a failure cutoff, pause,
throttle or concurrency limit. This maintenance did not edit that protected file.
