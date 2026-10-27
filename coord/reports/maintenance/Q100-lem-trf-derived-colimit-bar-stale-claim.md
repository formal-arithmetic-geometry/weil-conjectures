# Q100 stale claim maintenance: lem-trf-derived-colimit-bar

Recorded 2026-10-22T10:59:22Z by the pipeline maintenance engineer.

## Cause

Q94 completed the human-ordered stage-1 re-split in commit
68a629bcd4b8fa5b353fe556fa5c4ed26dde94e3 at 2026-10-22T08:24:36Z.
The accepted node is split, independently reviewed PASS by
NT-cc-Q94-35343c5df, with six new statement-only nodes and a
2514-character assembly. Its stage-1 repair note is resolved.

Q100 acquired a fresh claim at 2026-10-22T08:25:00Z, immediately after
that merge, and its first worker already reported superseded work.
The dispatcher retains the old stage 1 when claim.queue_stage returns
None and dispatches every held, undelivered item again. A stale queue
snapshot explains the post-merge assignment; the retained server claim
is the confirmed reason the retries continued after queue refreshes.
The 52 failures at maintenance dispatch were bookkeeping failures.
The empty sandbox and dry-run error were consequences of correctly
refusing to duplicate accepted work, not missing mathematical work.

## Repair

Under coord/.merge.lock with SHEAF_LEAD=L-only, verified the committed
reviewed node, resolved repair, stage-1 completion predicate, absence
from all three queue/tag files and rework holds, no Q100 return entry,
and no Q100 delivery branch. Removed only the obsolete Q100 claim:
coord/claims/lem-trf-derived-colimit-bar.lock.

Backup: /home/ubuntu/weil-maint-bak/Q100-lem-trf-derived-colimit-bar-20261022T105922Z/lem-trf-derived-colimit-bar.lock.bak

This report is new. No mathematical node, repair order, Lean source,
queue generator, launcher, review service or landing tool was changed.
No process was killed and no compiler or build was run.

## Instructions for future workers and launcher ownership

Stage 1 is complete. Reopen it only under a new released stage-1 repair
order; preserve Q94 completion and its six child nodes. Later-stage
work remains governed by its own queue and claims.

The launcher owner should reconcile already-held assignments against
current queue and stage completion: when an item is absent from the
queue, has no open return or delivery branch, and is complete for the
recorded stage with no released repair, retire its obsolete claim
instead of retaining the cached stage and launching it as new work.
This is completion bookkeeping, not a failure threshold, pause, cap,
throttle or admission limit. Keep the explicit human rule that listed,
unclaimed tasks are dispatched (claim.py commits 19a02c3a093 and
13f40e5d647). dispatch_all.py is launcher-owned and was not edited.

## Validation

Before removal: claim.node_finished(item, '1') was True,
claim.queue_stage(item) was None, and Q100 still held the item.
After removal: Q100 no longer holds it, and the normal claim path
rejects this unlisted, completed stage-1 item. The dispatcher will
observe the missing server claim on its regular refresh; no dispatcher
state, retry counter, retry delay, or process was manually changed.
