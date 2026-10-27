# NQ external-cup completed-stage routing repair

At 2026-10-23T21:50:16.153246+00:00, repaired the stale stage-1 assignment for `lem-sfb-flat-space-derived-external-cup`.

Q33's accepted split is server commit
`5265ef6fc247100c7f7527abf7649eebb567c445` (2026-10-24 04:44:20 +08),
reviewer `NT-cc-Q33-8765bd215`, ten proof steps, zero new nodes. The current
node's SHA-256 is `4d8f3a2b74fe81e59652a8851366f71b66d1b56e1b6998faac0fd5c97471a956`. Its mathematics and review are retained.
There is no released repair note, NQ delivery branch, or item return.

NQ acquired its stale claim at `2026-10-23T20:45:17Z`, 57 seconds after the
accepted merge. Repeated preserved-work dry runs then correctly rejected
the unchanged item. Before this repair, `claim.queue_stage` returned None,
`claim.node_finished(item, '1')` and `dag_queue.stage1_completed` returned
True, and all four working queue/tag records had removed the item. At initial
inspection the committed versions and launcher shared clone still advertised
it at stage 1. The held NQ claim plus the obsolete published stage kept it
dispatchable. During this investigation the ordinary build commit
`267493a23d23d744891752b17165933a19f7fe10` (05:48 +08) also published
a queue removing this item. By this maintenance commit its parent HEAD
already omitted the item; the final publication below advances the current
generation and the claim cleanup completes reconciliation immediately.

Published the four already generated current queue/tag files together, with
3898 matching item IDs in the queue and both batch-tag files. These
are ordinary current generated data, not retry suppression or a new pause.
Removed only the obsolete NQ claim, after rechecking completion, ownership,
no repair note, no return and no delivery branch under the merge lock and
claim takeover lock. Other claims and dispatcher state were not edited.

Existing working queue/tag files, their previous HEAD contents, and the
removed claim have adjacent `.maint-NQ-external-cup-1792791395.bak` backups (HEAD backups include
`.HEAD.`). This note is new. The commit includes only the four queue/tag
records and this note, plus the tracked claim deletion.

General owner follow-up: `merge_delivery.refresh_queue` defers refresh to
`local/stage2/queue-requested` when parallel landing is enabled. The
`~/cc1/sorry-route-loop.sh` consumer rewrites queue/tag files without
publishing them in git. `dispatch_all.Group.server` retains the old stage
when the live queue has no row, while `_listed` and `start_admitted` consult
the stale committed queue in the shared clone. The protected landing/launcher
owners should publish coherent background queue/tag generations or reconcile
held assignments against authoritative live stage completion. No protected
tool was changed, and no cap, throttle, retry cutoff or pause was added.

Next worker: stage 1 is already complete; preserve Q33's reviewed split.
Do not redeliver the identical sandbox node or manufacture a repair note.
Resume work only at an actually open next stage or under a substantive
released repair order. The dispatcher automatically deleted the old sandbox after the claim
was removed (its ordinary unclaimed-sandbox cleanup, dispatch_all.py:872).
The attempted sandbox-report handoff therefore made no write. Q33's
accepted node and report remain in the repository, and historical NQ
worker logs remain under the launcher's run/NQ directory. The full final
maintenance report is in the maintenance working directory as REPORT.md. No Lean source changed; no compiler or Lake build was needed.
