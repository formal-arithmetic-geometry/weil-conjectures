# Q15: completed stage-1 item with a stale claim

Maintenance time: 2026-10-22T19:51:53.946516+00:00.

Item: `lem-sf-weil-verdier-dual-preserves-weil-complexes`. Q03's accepted re-split landed in `561683c6acf0f9c2d789a3964041338d70142ab1` at 2026-10-22 09:40:59 UTC (completion log: 09:40:58 UTC; delivery `02eeff96a49`; independent reviewer `NT-cc-Q03-02eeff96a`). It added `lem-sf-weil-verdier-module-constructibility-comparison` and `lem-sf-weil-geometric-hom-constructibility`.

Q15's claim was created at 2026-10-22T09:41:06Z, eight seconds after the completion log, and was subsequently committed by `37cac849644` (build bookkeeping). The live node is split and reviewed PASS, the stage-1 repair is resolved, stage1_completed is true, stage1_repair_owed is false, queue_stage is None, and there is no Q15 delivery branch or open return. The dispatcher recorded 39 failures at maintenance start; all 44 retained run directories end BLOCKED for this already accepted split or the unchanged-item preflight.

Cause: a claim outlived its queue assignment. `dispatch_all.py:Group.server` reads queue stage '-' and retains the remembered stage 1; `Group.work` then retries the held claim without rechecking stage-1 completion. The worker's live-wins rule and preflight are correct. The initial claim followed the landing before queue reconciliation; current claim.take explicitly honors listed items.

Under coord/.merge.lock, rechecked all completion, queue, ownership, branch and return conditions, made byte-for-byte backups, and ran the standard `tools/claim.py release Q15` command. Only the obsolete claim and its release log were changed, with this maintenance note. No mathematical node, repair, review, Lean module, worker sandbox, dispatcher state or protected launcher/landing tool was edited. No compiler or build was needed for this bookkeeping repair. No process was signaled and no dispatch restriction was added.

Release record:

2026-10-22T19:51:53Z Q15 released lem-sf-weil-verdier-dual-preserves-weil-complexes: maintenance: stale stage-1 claim; Q03 split accepted at 561683c6acf, repair resolved, no queue row or open delivery/return; reconcile completed assignment

Backups (server-local, intentionally not staged; the new note's backup records its prior absence):

- `/home/ubuntu/weil-conjectures-sheaf/coord/claims/lem-sf-weil-verdier-dual-preserves-weil-complexes.lock.maint-Q15-20261022T195153Z.bak`
- `coord/deliveries.log.maint-Q15-20261022T195153Z.bak`
- `coord/maintenance/20261022-Q15-weil-verdier-stale-claim.md.maint-Q15-20261022T195153Z.bak`

Unchanged SHA-256 values:

- `/home/ubuntu/weil-conjectures-sheaf/dag/nodes/sec-six-functors/lem-sf-weil-verdier-dual-preserves-weil-complexes.json`: `144a3784e7965cb8f88b842bef444c7489eb174bf3b78732c91da8a64e3ecea0`
- `coord/repair-notes/lem-sf-weil-verdier-dual-preserves-weil-complexes.json`: `be3fd9a5b68a57607586d97305c515e26a67b6153c30d28828b61d3a7cd41ef0`
- `lean/WeilConjectures/WeilSheaf/VerdierDual.lean`: `b564d8b2d198fe0218b3fa02e0a55b9273822eb3dc04b3e762619fa83a2bce7c`

Launcher follow-up (report only; dispatcher is protected): reconcile held stage-1 claims with live stage1_completed and stage1_repair_owed before retrying a claim that is absent from the queue. Respect explicit open returns, delivery branches, newly released repairs, and the human's requirement to dispatch listed unclaimed items. Do not use failure counts as a cutoff or add limits, throttles, waits or pauses.

Next worker: stage 1 is complete. Reuse Q03's accepted split. Only a newly released stage-1 repair or a new explicit queue assignment calls for further stage-1 work. The sorry in VerdierDual.lean is later-stage work and does not authorize resplitting this completed item.
