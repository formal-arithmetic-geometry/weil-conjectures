# NL semilinear slice scalar generators: stale claim reconciliation

On 2026-10-22, stage 1 of `lem-sf-semilinear-slice-scalar-generators` was
completed by Q67 and accepted in `20887dbc991` at 07:12:47 UTC. The delivery
was `8bafb5fc0d7`; the independent reviewer was `NT-cc-Q67-8bafb5fc0`.
The node is `split` with a passing review. There is no repair note, open NL
return, or NL delivery branch. The live queue has no row for this item.

NL's claim was created at 07:13:33 UTC, 46 seconds after the accepted landing,
from a stale queue/assignment snapshot. `claim.take` intentionally grants
listed unclaimed work (human's 2026-10-22 rule). Once the queue removed this
completed item, the held claim remained. `Group.server` reported stage `-`,
so `dispatch_all.py` retained its cached stage 1; `Group.work` repeatedly
relaunched the claim without checking stage-1 completion. The worker correctly
obeyed the stage-1 live-wins rule. The missing sandbox node and dry-run failure
were consequences, not a mathematical or permission failure.

Under `coord/.merge.lock`, backed up the NL claim and `coord/deliveries.log`,
then used `tools/claim.py done NL <item> <reconciliation reason>` to close only
this obsolete claim. This records completion of the assignment by reference
to Q67's accepted landing; it does not claim a new NL mathematical delivery.
The reconciliation is also in `coord/deliveries.log`. That generated log had
pre-existing edits, so it is left to the normal maintainer snapshots; this
commit includes only the claim deletion and this maintenance record.

Validation at reconciliation: stage-1 completion is true; queue stage is
absent; the claim is absent and NL no longer holds it. The node SHA-256 is
`72f6afd17f962bc8a336b7c379eab3eb7ac2a67125dc181b43c479f299cd8899`. No DAG, Lean, worker report, brief, repair note, launcher code,
review service, or landing tool was changed. Existing files have adjacent
`.maint-NL-semilinear-1792659170.bak` backups; this new note also has a `.bak` copy.

Launcher follow-up (report only, protected code): reconcile a held stage-1
claim after its live queue row disappears, once the live completion predicate
confirms it is done and no explicit return or released stage-1 repair reopens
it. An absent/failed queue read alone is insufficient. Preserve the human's
rule to dispatch listed unclaimed work. Never gate on failure counts, and do
not introduce a cap, throttle, admission limit, or pause.

Next worker: this stage-1 split is already accepted. Do not re-split, fabricate
an attachment, create a repair note merely to justify this stale dispatch, or
copy the accepted node into an unchanged delivery. New stage-1 work requires
an actual released stage-1 repair order. Stage 2 remains a separate obligation
and should proceed when the normal dependency queue makes it ready.
