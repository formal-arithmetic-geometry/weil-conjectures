# Retire obsolete NE stage-1 claim

Item: `lem-sp-proetale-direct-image-scalar-cocycle`.

Q09's stage-1 repair was accepted at 2026-10-22T06:18:54Z, commit
`922823cae6a` (delivery `9e54fca94ad`, reviewer `NT-cc-Q09-9e54fca94`).
Its two normalization children are already in the live DAG and its repair note
is resolved. NE acquired another claim at 2026-10-22T06:19:35Z during the
queue-refresh interval. Once the queue removed the completed item, that claim
remained. The dispatcher kept its saved stage 1 because queue_stage returned
None, then repeatedly launched unchanged-item preflights. The counted failures
are a stale claim, not an outstanding stage-1 mathematical obligation.

The maintenance run waited for NE's worker to exit naturally, backed up the
claim and delivery log, and released only this obsolete claim under the merge
lock. It did not change the accepted node, repair order, Lean, worker sandbox,
or failure counters. No process was killed.

The human's policy that every listed, unclaimed item is dispatched is retained.
The launcher-owned dispatch_all.py needs reconciliation of already-held
stage-1/2 claims: when an item is absent from the current queue, has no open
return or delivery branch, has no released repair note, and the live node is
complete for the saved stage, release its obsolete claim after any worker exits.
Read-only completion checks and failure counts must not block listed work.
Maintenance did not edit launcher-owned code.

Any later stage-1 worker should first check for an actual released repair note.
Without a new repair, retain Q09's accepted split; work on its children or a
separately queued Lean obligation belongs to the relevant assignment.

## In-flight dispatcher pass reconciled

The first retirement committed at `6e975348407` waited for the merge lock.
A dispatcher pass already in progress started one more worker before that
release completed. Maintenance temporarily restored the original claim from
its backup so the dispatcher would allow that worker to finish naturally.
After the worker exited, the claim was released again using nonblocking
acquisition of the existing merge lock. No process was killed and no dispatcher
state or failure count was reset. The final release is in deliveries.log.
