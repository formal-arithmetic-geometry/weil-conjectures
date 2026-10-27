# NJ derived Weil adjunction: stale stage-1 claim

Item: `lem-sf-derived-weil-pullback-pushforward-adjunction`. Maintenance run: NJ-1792647586, 2026-10-22.

Cause: Q31's delivery `12c2f96f45b` was independently reviewed and landed as
`0694b61557fab6a6598b7f16036901e3dc604d17` at 2026-10-22 05:11:34 UTC.
The committed queue at that merge still listed the item in stage 1. NJ obtained
a claim at 05:11:40 UTC. The current queue no longer lists the item, the live
node is split/reviewed PASS, and no released repair note, NJ return, or NJ
delivery branch requires work. However, the dispatcher retries held claims,
retaining its stored stage when `claim.queue_stage` returns None. It repeatedly
assigned stage 1 and the delivery preflight correctly refused an unchanged node.
This is stale bookkeeping, not a mathematical or compiler failure.

Repair: checked the live node, reviewed merge, queue, claim and repair/return
records under the merge lock, then used `tools/claim.py done NJ lem-sf-derived-weil-pullback-pushforward-adjunction`
with a maintenance explanation to close NJ's stale claim. The normal tool
appended the completion record to `coord/deliveries.log`. This report is the
committed maintenance record; pre-existing unrelated uncommitted log entries
are left for normal bookkeeping commits rather than included in this commit.
The node's SHA-256 was unchanged across the repair: `a40c2e7435ed72b2fa4b981b5449df294f269c50514550c9ce6e8b2df8793d28`.

Backups, made before the operation:

- `coord/claims/lem-sf-derived-weil-pullback-pushforward-adjunction.lock.maint-NJ-1792647586.bak`
- `coord/deliveries.log.maint-NJ-1792647586.bak`

Verification: the claim is absent, `claim.held_by('NJ')` excludes the item,
`claim.queue_stage(item)` is None, `claim.node_finished(item, '1')` is True,
and `dag_queue.stage1_repair_owed(item)` is False. No Lean file was changed or
compiled. No worker process was signalled, no failure counter was reset, and
no dispatch pause, throttle or concurrency limit was added.

Launcher follow-up (not applied; dispatch_all.py is protected): in
`Group.server`/`Group.work`, reconcile held stage-1 claims whose queued stage
has disappeared against the server's `dag_queue.stage1_completed` predicate
before launching another new worker. Only close completed assignments without
an outstanding repair, return or delivery. Preserve legitimate unqueued work
and the human's rule that listed, unclaimed items are dispatched. Failure
counts must remain irrelevant to eligibility. The race can recur for other
items until the launcher implements this stage-aware reconciliation.

Next worker: stage 1 is complete; do not split again, manufacture a node diff,
or repeat the unchanged-node dry run. Continue the native prerequisites or a
future explicitly queued stage-2/repair task. The old source.place attachment
language is historical, not proof that an attachment is sorry-free; prior
attachment checks rejected the claims. This maintenance does not certify a
Lean attachment. The existing NJ sandbox is preserved.
