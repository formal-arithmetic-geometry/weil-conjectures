# Q30 superseded stage-1 claim repair

Recorded 2026-10-23T03:57:17.785532+00:00.

The repair of `lem-zl-morphism-open-closed-reduction` was merged as `95cb040706b` at 2026-10-22T04:29:55Z by Q15, reviewed PASS by NT-cc-Q15-1a3f19791. That commit also resolved its stage-1 repair note. The six-step split and seven supporting nodes are already delivered.

Q30 obtained a stale stage-1 claim at 2026-10-22T04:30:28Z, 33 seconds later. The claim has a 72-hour TTL. The current server queue and batch tags have no row for the item, `claim.node_finished(item, "1")` is true, the repair note is resolved, and there is no Q30 delivery branch or open return. Nevertheless, dispatcher `Group.server()` leaves the saved stage unchanged when `queue_stage` returns None; `Group.work()` restarts held stage-1 items without the completion checks it has for stage 3. This produced the 111 counted failures and the repeated correct preflight rejection, "the item's node file is unchanged".

Used the normal `tools/claim.py release Q30` operation to remove only this superseded ownership record. The original claim and deliveries log have adjacent `.maint-Q30-20261023.bak` copies. A complete local sandbox archive and dispatcher-state backup are in `/home/ubuntu/weil-launcher-all/maint/Q30-lem-zl-morphism-open-closed-reduction-1792727601/evidence/`. The live node and resolved repair order are unchanged.

This is completed work leaving dispatch, not an attempt limit, pause, throttle, or abandonment. Do not resplit, cosmetically edit, or deliver an unchanged copy. Reopen stage 1 only with a new explicit released stage-1 repair order.

The general dispatcher repair is documented in that maintenance directory's `REPORT.md`. The user prohibits editing `dispatch_all.py` in this task. A launcher maintainer should revalidate completed, off-queue stage-1 held claims before restart and release stale ownership through claim.py, honoring released repair orders and active returns/deliveries. Preserve historical failure counts.

Original claim: `{"who": "Q30", "t": 1792643428.0774355, "since": "2026-10-22T04:30:28Z"}`.
Live review: `{"date": "2026-10-22", "by": "L", "reviewer": "NT-cc-Q15-1a3f19791", "group": "Q15", "result": "pass", "note": "mechanical checks by tools/merge_delivery.py; mathematics reviewed i` (full review is in the node).
Released record: `2026-10-23T03:57:17Z Q30 released lem-zl-morphism-open-closed-reduction: maintenance: superseded stage-1 claim; Q15 reviewed split 95cb040706b resolved the repair; no queued or returned work remains`.
