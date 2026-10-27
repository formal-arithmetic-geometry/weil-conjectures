# NS stale stage-1 claim: ground-field retagging

The accepted Q153 repair is commit `d415e87942e`: the item is split and independently reviewed PASS, with two new nodes, and its stage-1 repair record is resolved. `coord/deliveries.log` records completion at 2026-10-22T06:51:58Z. NS acquired a new claim at 06:52:12Z, fourteen seconds later. The live queue no longer lists the item, but that claim persisted.

The launcher reads held claims even when absent from the current queue. `Group.server()` updates a held item's saved stage only when a queue stage exists; `Group.work()` retries held stage-1 items without checking live completion. Consequently NS retained stage 1 and repeatedly received an instruction prohibited by the standing brief: splitting an already accepted node without a released repair order. Failure counts did not cause or justify stopping dispatch.

Maintenance checked the live node, resolved repair, absence from every queue, and absence of any NS delivery branch or open return. Under `coord/.merge.lock`, it backed up the claim and deliveries log with suffix `.maint-NS-1792665441.bak`, then used `tools/claim.py release NS` with an explicit completed-work reason. This closes an obsolete assignment; it introduces no throttle, pause, failure limit, or mathematical change. The standing brief and accepted split are correct.

Launcher follow-up (launcher-owned code was not edited): in `dispatch_all.py`, reconcile held stage-1 claims with live stage completion when the item is no longer queued, respecting released stage-1 repairs and active deliveries/returns. A missing queue stage must not preserve an obsolete stage-1 assignment indefinitely. The current claim tool refuses a new explicit stage-1 claim for this off-queue completed item. Continue normally if a later authorized queue or repair order reopens work.

A future stage-1 worker must preserve Q153's accepted split. Re-split only under a newly released stage-1 repair order. Stage 2 is a separate task and must use its own queue stage and brief.
