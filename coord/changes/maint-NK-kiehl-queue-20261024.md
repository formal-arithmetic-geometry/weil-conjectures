# NK maintenance: completed Kiehl item dispatched as stage 1

Item: `lem-sfb-kiehl-relative-pseudocoherent-direct-image`. Maintenance date: 2026-10-24 (+08).

N0's accepted stage-1 split is commit `d51b3bc24daa9073bb027b6fd41b7380333f15f1`
(delivery `259303eb23b`, reviewer `NT-cc-N0-259303eb2`, result pass).
NK obtained its stale claim at `2026-10-23T18:51:47Z`, 25 seconds after that landing.
There is no released repair note reopening stage 1. The worker's refusal to resplit is correct.

The live working queue already omitted the item, but the committed queue last published at
`7cf37fcd733` still listed it at stage 1. The shared clone follows committed `sheaf-dag`,
so the dispatcher's `_listed` and `_queue_stage` checks kept seeing the obsolete stage-1 row.
When `claim.queue_stage` on the live server finds no row, the dispatcher retains the old
recorded stage. Thus a stale NK claim plus an unpublished queue repeatedly restarts stage 1.

Repair: publish the four already generated queue/tag records in this commit and remove the
stale NK claim (removed in this maintenance: True). No accepted split or Lean file changes.
Every existing file touched or published is backed up beside itself with suffix `.maint-NK-kiehl-20261024T0333.bak`;
the former committed queue/tag versions also have `.HEAD.maint-NK-kiehl-20261024T0333.bak` backups.

Protected-tool follow-up for the launcher owner: `tools/nt_land_batch.py` calls
`merge_delivery.refresh_queue`; with `local/stage2/parallel-enabled` present it only touches
`local/stage2/queue-requested`. `/home/ubuntu/cc1/sorry-route-loop.sh` regenerates the queue
and tags, but never commits those records. Publish coherent queue/tag snapshots under the
merge lock after this background refresh, or make dispatcher completion reconciliation use
the authoritative live queue rather than stale committed rows. These are protected landing/
launcher paths and were not edited. Do not add a retry limit, pause, or concurrency restriction.

Next worker: this item is complete at stage 1. Do not resplit, fabricate a repair note, or
redeliver N0's work. Future work requires an actual open stage or released repair scope.
