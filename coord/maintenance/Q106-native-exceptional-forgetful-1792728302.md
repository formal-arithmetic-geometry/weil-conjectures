# Q106 maintenance: native exceptional forgetful assignment

Item: `lem-sf-weil-native-exceptional-forgetful`; dispatcher key `lem-sf-weil-native-exceptional-forgetful@new`; 37 counted failures.
Maintenance timestamp: 2026-10-23T04:10:40.640122+00:00.

## Cause

Q88's reviewed four-node split landed in `a42c2715260` at
2026-10-22T09:31:35Z. Its stage-1 repair is resolved. Q106 acquired the
superseded stage-1 assignment at 09:31:49Z, 14 seconds later, from a stale
queue snapshot. The first Q106 worker already reported the accepted live split.
The unchanged-file preflight failures are correct: another split is forbidden
by the live-wins rule in `coord/brief-stage1.md`.

The retained Q106 claim outlived the queue row. `Group.server()` in the launcher
updates a cached stage only when `claim.queue_stage()` returns 1, 2, or 3.
When it returns None, cached stage 1 survives. `Group.work()` relaunches held,
undelivered claims without checking whether stage 1 is already completed.
Consequently this item kept receiving the obsolete stage-1 brief.

Immediately before repair, the server reported stage1_completed=True,
claim.node_finished(item, '1')=True, queue_stage=None, repair state=resolved,
and an unexpired Q106 claim. No Q106 return or delivery branch existed.
The item has no Lean record yet; this is stage-1 completion only.
The read-only DAG diagnostic found the unstated statement dependency
`lem-sf-adic-qbar-constructible-realization`, explaining why formalization
is not currently queued. No scheduling restriction was added.

## Applied correction

Released only the obsolete Q106 claim using:
`python3 tools/claim.py release Q106 lem-sf-weil-native-exceptional-forgetful '<maintenance reason>'`.
The release is recorded in `coord/deliveries.log`. This is a completed
assignment reconciliation, not an abandonment or a failed mathematical result.
The node, accepted Q88 review, resolved repair, Lean source, worker sandbox,
and dispatcher history were preserved. No process was stopped.

The claim and deliveries log were backed up before mutation:
- `/home/ubuntu/weil-conjectures-sheaf/coord/claims/lem-sf-weil-native-exceptional-forgetful.lock.maint-Q106-1792728302.bak`
- `coord/deliveries.log.maint-Q106-1792728302.bak`

## Verification

After release, claim.read(item)=None, the item is absent from Q106's held
claims, queue_stage remains None, and an explicit stage-1 claim attempt
is refused as already completed. The accepted node and repair record are
byte-identical to their pre-repair copies. Node SHA-256:
`40a19e780ee5056b3a440d56ecd9eb0e4e2c6012d07e816bb0a64517c77b2cb4`.
No Lean source changed, so no Lean compilation was needed.

## Launcher follow-up (protected code; not edited)

In `/home/ubuntu/weil-launcher-all/dispatch_all.py`, reconcile already-held
stage-1 assignments against the server's completion predicate before relaunch.
If there is no current queue row and stage1_completed is true with no released
stage-1 repair and no delivery/open return, release the obsolete claim rather
than use its cached stage. Preserve failure counters as history. If the live
queue supplies a different stage, use that stage and its own brief, without
carrying stage-1 BLOCKED guidance into it. Add a regression covering a reviewed
split, resolved repair, cached stage 1, and absent queue row. Keep the human's
queue-wins rule for currently listed items and all legitimate unfinished work.
No failure-count cutoff, concurrency cap, throttle, admission limit, or pause.

## Next worker

Retain Q88's accepted split and its four obligations. Do not edit or re-deliver
an unchanged split just to clear preflight. An eventual worker must follow the
current queue stage: formalization has a different brief and sandbox. Only a
new released stage-1 repair can reopen this split. The old Q106 sandbox is
historical evidence, not a pending delivery.
