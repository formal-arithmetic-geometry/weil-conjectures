Q30 maintenance, 2026-10-23: lem-pur-weil-tate-datum-transport

Released the obsolete Q30 claim for completed stage 1 using tools/claim.py release.
Q157's accepted split is commit 65864665b62; coord/deliveries.log records its
merge at 2026-10-22T06:59:43Z, reviewer NT-cc-Q157-fba2c633d. The stage-1 repair
record is resolved. The Q30 claim was created at 2026-10-22T07:00:54Z, 71 seconds
after that merge. It remained valid under the configured 72-hour claim TTL.

At repair time the node has status split, review pass, lean null; the canonical
claim.node_finished(item, '1') predicate is true and its stage-2 predicate is
false. The current queue contains no row for this item. There is no Q30 return
entry or delivery branch, and no active Q30 worker on this item was recorded by
the dispatcher. The claim exactly matched the original recorded assignment.

The dispatcher enumerates held claims even when they are absent from the queue.
Its server() updates saved stages only when queue_stage returns 1, 2 or 3;
otherwise work() reuses the saved stage 1. Stage-1 held work has no completion
reconciliation, so the same closed assignment repeatedly produced BLOCKED.
The worker correctly followed the live-wins and no-post-merge-delivery rules.

Backups before release:
- coord/claims/lem-pur-weil-tate-datum-transport.lock.maint-Q30-tate-datum-20261023.bak
- coord/deliveries.log.maint-Q30-tate-datum-20261023.bak

The commit removes only this stale claim, records this release and adds this
note. Pre-existing uncommitted deliveries.log additions are kept unstaged.
The accepted node, its review, repair note, sandbox and mathematics are preserved.
No Lean source changed and no compilation was needed.

Next worker: stage 1 is complete. Use the normal live queue for later-stage work;
do not duplicate Q157's split. No skip, abandonment, hold, limit or pause was added.
The launcher-owned dispatcher needs a general completion reconciliation for held
stage-1 claims; that protected code was not edited by this maintenance task.
