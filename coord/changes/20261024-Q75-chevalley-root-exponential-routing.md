# Q75 maintenance: completed Chevalley root exponential item dispatched again

Item: `lem-sfb-chevalley-root-exponential-group`, stage 1.

## Cause

Q06's split was accepted as `f98eb8bba83524c1272f78bc947a07b8ea244b8a`
(2026-10-23 21:50:45 UTC), reviewer `NT-cc-Q06-a128395c4`, result `pass`.
The node has no released repair note and is completed for stage 1.
Q75 acquired a fresh claim at 21:50:50 UTC, shortly after that merge.
Its repeated dry runs correctly rejected an unchanged node. The brief correctly
prohibited re-splitting a reviewed node without a released repair order.

The live generated server queue excluded the item, but the committed queue last
published at `ef1aa515460ce755c1cb5a7f563805b2df6efe27` still included its stage-1 row.
The launcher shared clone resets to Git, so refreshing it retained that old row.
`dispatch_all.py` reads the live queue for new work, but `Group.work` uses
`_listed(shared_clone, item, stage)` for held work and `start_admitted` uses
`_queue_stage(shared_clone, item)`. That inconsistent source kept restarting Q75
instead of recognizing the completed item. Preflight was working correctly.

## Repair

Published the current, already generated queue and both batch maps in
`d234b182ddd80dc0343a3c591beaf8410c58a7a6`:
`coord/queue.tsv`, `coord/queue.md`, `coord/queue-batches.tsv`, and
`coord/queue-batches-all.tsv`. Their 4,002 rows comprise 292 stage-1, 2,815 stage-2,
and 895 stage-3 items; batch-map coverage and Markdown totals were checked.
The completed item is absent from all four records. This publishes current
computed data; no queue-selection rule changed.

After the active worker exited naturally at 2026-10-23 22:47:07 UTC,
released only its stale Q75 claim with `tools/claim.py release`. The release
entry is committed separately from other pending delivery-log entries.
All existing changed files have backups ending in
`.maint-Q75-root-exponential-1792794847.bak`; each queue record also has a
`.HEAD.maint-Q75-root-exponential-1792794847.bak` committed-version backup.
The untracked claim's backup remains beside its former path in `coord/claims/`.

## Verification and next worker

The shared clone refreshed to the published queue and no longer lists the item.
`claim.queue_stage(item)` is `None`, `claim.node_finished(item, "1")` is `True`,
and the stale claim is gone. The mathematical node is byte-for-byte equal to
its accepted Q06 version. No Lean sources changed and no compiler was run.
There is no Q75 delivery branch or open item return to repair.

Do not manufacture a node edit or re-split this item. Stage 1 is complete;
future work requires a genuine released repair order or later-stage eligibility.
Retained sandbox reports/citations remain diagnostic history.

## Launcher follow-up (protected files unchanged)

Use the same successfully fetched live queue snapshot for held-item membership
and stage selection as for new dispatch in `dispatch_all.py` (`Group.work`,
`start_admitted`, `_listed`, `_queue_stage`). A shared Git checkout is not a live
queue mirror while queue rewrites are uncommitted. Alternatively, the queue
publisher must consistently publish queue snapshots to readers after rewrites.
The general source mismatch can recur for other completions until the launcher
owner fixes it. No launcher, admission, review, or landing tool was modified;
no concurrency limit, throttle, or pause was added.
