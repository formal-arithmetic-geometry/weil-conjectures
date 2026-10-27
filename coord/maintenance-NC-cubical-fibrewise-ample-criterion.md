# Completed stage-1 item repeatedly dispatched to NC

Item: `lem-sfb-cubical-fibrewise-ample-criterion`.

Q06's reviewed split landed in `21109b7fbc7` at 2026-10-23T23:49:25Z
(delivery head `1a5631d5a7a`, reviewer `NT-cc-Q06-1a5631d5a`).
There is no released stage-1 repair note and no open return for NC on this item.

The server working queue correctly excludes the item. The last committed queue,
`711e4433293` (2026-10-23T23:21:32Z), still listed it at stage 1. The launcher's
`Group.work()` and `start_admitted()` consult `coord/queue.tsv` in the shared
clone, which refreshes committed files only; the server queue read by
`Group.server()` no longer supplied a stage and the recorded stage 1 survived.
NC therefore repeatedly restarted the stale held claim and obeyed the brief's
live-wins rule by returning BLOCKED. All completed NC retry records inspected
were answered, with zero recoveries and no provider error.

Maintenance regenerates the batch tags from the current queue, publishes the
four mutually consistent queue records, and releases only NC's obsolete claim
using `tools/claim.py release`. This is completion reconciliation, unrelated to
failure counts. No node, proof, Lean source, review, or launcher code is changed.

The launcher owner should change the protected `dispatch_all.py` so held-item
eligibility and stage selection use the successfully read live server queue,
not a committed-clone queue that can lag working queue regeneration. Preserve
legitimate released repair orders and keep dispatching actual unfinished work;
add no failure threshold, backoff, pause, or concurrency restriction. Queue
publication after regeneration is the other ownership boundary to make reliable.

Next worker: stage 1 is already accepted. Do not split or redeliver it without
a released stage-1 repair note. Let the live queue schedule later stages when
their dependencies are ready.

Backups (before maintenance writes/release):
- `coord/queue.tsv.maint-NC-cubical-20261024T004802Z.bak`
- `coord/queue.md.maint-NC-cubical-20261024T004802Z.bak`
- `coord/queue-batches.tsv.maint-NC-cubical-20261024T004802Z.bak`
- `coord/queue-batches-all.tsv.maint-NC-cubical-20261024T004802Z.bak`
- `coord/deliveries.log.maint-NC-cubical-20261024T004802Z.bak`
- `/home/ubuntu/weil-conjectures-sheaf/coord/claims/lem-sfb-cubical-fibrewise-ample-criterion.lock.maint-NC-cubical-20261024T004802Z.bak`
