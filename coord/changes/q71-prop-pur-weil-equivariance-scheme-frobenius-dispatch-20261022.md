# Q71 obsolete stage-1 dispatch cleanup

Maintenance: 2026-10-22T14:40:27.853195+00:00. Item: `prop-pur-weil-equivariance-scheme-frobenius`.

Q148's split was independently reviewed PASS by NT-cc-Q148-50bb94344 and
merged at `08524667bdd`; `coord/deliveries.log` records completion at
2026-10-22T06:51:52Z and `coord/ledger.md` records it at 06:51. The stage-1
repair note is resolved. The live node has status split and the item is absent
from `coord/queue.tsv`; neither Q71 nor Q148 has an open return or delivery
branch for this item.

Q71 nevertheless held a claim with since=2026-10-22T06:52:12Z
(t=1792651932.516714), acquired 20 seconds after the completion log.
The launcher's held-claim path keeps the saved stage when queue_stage returns
None, and relaunches it as new without checking stage-1 completion. This
produced at least 68 failures while workers correctly honored the live-wins
rule. Their dry-run error, no node files, was a consequence of the obsolete
assignment; there was no new split to submit.

Released only Q71's obsolete claim with the normal `tools/claim.py release`
command, using a maintenance reason (no abandonment or new completion claim).
The release is recorded in `coord/deliveries.log`. The accepted DAG node,
its review, and the resolved repair note were preserved.

Backups before mutation:
- `coord/claims/prop-pur-weil-equivariance-scheme-frobenius.lock.maintenance-Q71-1792679810.bak`
- `coord/deliveries.log.maintenance-Q71-1792679810.bak`

Do not dispatch a new stage-1 split unless a new live queue entry or a released
stage-1 repair order reopens it. Do not copy Q148's accepted split into a
new delivery. Stage 2 remains governed by its normal dependency/queue rules.

The launcher-owned `dispatch_all.py` was not edited. Its owner should
reconcile held DAG assignments with live completion when they leave the
queue, preserving open returns and explicitly reopened repairs. This is a
completed-assignment cleanup, unrelated to failure counts or scheduling limits.
