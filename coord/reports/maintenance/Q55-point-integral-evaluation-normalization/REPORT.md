# Q55 obsolete stage-1 claim repair

Date: 2026-10-22T13:34:44Z
Item: `lem-pod-point-integral-evaluation-normalization`. Dispatcher key: `lem-pod-point-integral-evaluation-normalization@new`.

Cause: Q51's split was accepted at 2026-10-22T09:16:51Z, commit
`944659b3fd90b098edb8018e8e83838342ef79a7`, reviewer `NT-cc-Q51-d57aadaa7`.
Q55 acquired its claim at 09:17:04Z, 13 seconds after that landing, and
started a new stage-1 worker. This is a stale assignment after a landing,
not a failed mathematical split. Every completed attempt inspected reports
the same accepted-split/no-repair conflict. The failure count has no bearing
on whether work should run.

The live node is `split`, independently reviewed `pass`. The server's
`dag_queue.stage1_completed(node)` and `claim.node_finished(item, '1')`
both return True. `claim.queue_stage(item)` is None; no repair note,
Q55 open return or Q55 delivery branch exists. The retained Q55 sandbox
has a disposition report but no proposed DAG split.

The protected launcher's `Group.server()` only replaces its cached stage
when the queue supplies a numeric stage; a missing queue row retains stage 1.
`Group.work()` then relaunches held stage-1 claims without testing live
completion. It does have completion/off-queue reconciliation for stage 3.
Thus the obsolete Q55 claim kept producing BLOCKED answers and immediate
retries, rather than being retired as completed work. At task start the
dispatcher counted 56 failures; it continued dispatching while maintenance
ran. No provider failure is the cause of this item.

Repair: backed up and released only the obsolete Q55 claim with the
project's `tools/claim.py release` command, and recorded the disposition
in `coord/deliveries.log`, `coord/ledger.md`, and this report. These paths,
including deletion of `coord/claims/lem-pod-point-integral-evaluation-normalization.lock`, are committed together
under `SHEAF_LEAD=L-only flock coord/.merge.lock` with the required identity.
The accepted node, its statement, six-step proof, review, worker sandbox,
failure counters, queue, briefs and launcher code are unchanged.

Backups: `local/maintenance/Q55-point-integral-evaluation-normalization-1792675635/` contains the original claim, deliveries.log and
ledger.md, each with a `.bak` suffix. This report is newly created.
Node SHA-256 before and after: `45ad183879dc07b2f6c38362e1c69884364a9523014197b3894945f8a481f187`.

Verification: immediately before release, rechecked exact claim generation,
completion, queue absence, repair absence, return absence and branch absence.
After release, checked the claim is absent, Q55 no longer holds it, the item
remains off queue and completed, and the node hash is unchanged. No Lean file
was changed, so no Lean compilation is needed. No process was killed and
no concurrency cap, throttle, admission limit, backoff or pause was added.

Launcher-owned follow-up (required; file deliberately not edited):
`/home/ubuntu/weil-launcher-all/dispatch_all.py`, `Group.server/Group.work`,
must reconcile held stage-1 claims against live completion when the current
queue no longer lists the item. For an off-queue, accepted stage-1 item with
no released stage-1 repair, return or pending delivery, release its obsolete
claim through the claim tool and drop it from candidate work. An absent
queue row must not silently preserve a stale stage forever. Preserve queued
work, actionable repairs, and valid stage-2 transitions; use the live stage-1
completion predicate rather than failure counts. Add regression coverage
for an accepted split with a held cached stage-1 claim and no queue row,
alongside released repairs and valid stage-2 work. This general prevention
requires the launcher owner because the task prohibits editing this file.

Next worker: stage 1 is already accepted. Do not resplit or submit an unchanged
delivery without an explicit released stage-1 repair order. A future stage-2
assignment is separate and must follow the stage-2 brief; stage-1 acceptance
does not assert that a Lean proof exists. The old sandbox report is history,
not a repair order. Re-read live records if an actual new assignment arrives.
