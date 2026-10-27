# Completed stage-1 assignment: stale NA claim

Item: `lem-sfb-ordinary-proetale-direct-image-plus-comparison`. Maintenance performed at 20261022T124523Z UTC.

Q46's accepted stage-1 re-split landed at
`e7de4a3ec707e9fb8aaa84f69174eaf1f05bb8a3` on 2026-10-22 at
10:29:46 UTC (delivery head `3dd1f881a94`, independent reviewer
`NT-cc-Q46-3dd1f881a`). It added
`lem-sfb-additive-derived-plus-unit-normalization` and
`lem-sfb-constant-section-intrinsic-pullback-identification`.
The node has `status: split` and a passing review. The stage-1 repair note
is resolved. The accepted proof has five steps and 2966 characters.

The obsolete NA claim was created at 10:29:56 UTC, eleven seconds after
the completion entry in deliveries.log. At maintenance time the node was
absent from coord/queue.tsv, had no NA delivery branch or open NA return,
and tools/claim.py reported stage1_completed=true, stage1_repair_owed=false,
queue_stage=None. NA nevertheless retained its old stage-1 assignment,
so the dispatcher repeatedly restarted it. The live-wins rule in
coord/brief-stage1.md correctly prevented duplicate splitting.

Released only this stale NA claim with the standard tools/claim.py release
command. The completed split, review, repair note, Lean module and other
claims are unchanged. The release is bookkeeping, not a new delivery or
proof completion. No provider failure caused the recorded BLOCKED endings.

Launcher follow-up (the maintenance brief prohibits changing dispatch_all.py):
Group.server retains the old stage when claim.queue_stage returns None;
Group.work's held-claim loop rechecks completion for stage 3 but not stage 1.
It should retire held stage-1 claims once live stage1_completed is true and
there is no released stage-1 repair or open delivery/return requiring work.
Do not add failure cutoffs, throttles, pauses, or concurrency restrictions.

Next worker: this stage-1 assignment is complete. Reopen it only for an
explicit newly released stage-1 repair. Later-stage work must use the
appropriate stage and current queue rather than splitting this item again.

Release log entry:

2026-10-22T12:45:23Z NA released lem-sfb-ordinary-proetale-direct-image-plus-comparison: maintenance: stale stage-1 assignment; Q46 split accepted at e7de4a3ec707e9fb8aaa84f69174eaf1f05bb8a3, repair resolved, item absent from queue; remove obsolete claim, no new split required

Backups (existing files copied byte for byte; new-file backup records absence):
- `coord/claims/lem-sfb-ordinary-proetale-direct-image-plus-comparison.lock` -> `coord/claims/lem-sfb-ordinary-proetale-direct-image-plus-comparison.lock.maint-NA-20261022T124523Z.bak`
- `coord/deliveries.log` -> `coord/deliveries.log.maint-NA-20261022T124523Z.bak`
- `coord/maintenance/lem-sfb-ordinary-proetale-direct-image-plus-comparison-stale-claim-20261022.md` -> `coord/maintenance/lem-sfb-ordinary-proetale-direct-image-plus-comparison-stale-claim-20261022.md.maint-NA-20261022T124523Z.bak`
