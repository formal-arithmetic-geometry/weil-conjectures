# NA stale finite-immersion claim reconciliation (2026-10-22)

Item: `lem-sf-finite-immersion-constructibility-interval`, stage 1, dispatcher key `lem-sf-finite-immersion-constructibility-interval@new`.

Cause: NA still held the claim created at 2026-10-22T07:51:40Z, 22 seconds
after Q08's reviewed re-split merged at 07:51:19Z in `5da4b876cd0533b36cf9bf608282869a6cae596f`.
The dispatcher recovers held claims even off queue and, when queue_stage returns
None, retains the saved stage 1. Each worker therefore received a finished
stage-1 assignment, copied the accepted node, and correctly hit preflight's
"the item's node file is unchanged" refusal. Failure counts did not cause this.

Evidence: reviewer NT-cc-Q08-45fcc5238 PASS; stage-1 repair note resolved;
stage1_completed and node_finished(stage 1 and stage 2) true; queue_stage None;
no NA delivery branch or return for this item. N8's reviewed stage-2 binding
remains Sheaf.Paper.FiniteImmersionConstructibilityInterval (batch commit
3dae427af7e11a83cb3a5bbc4f497ee632f722bd). Existing worker logs and retained
sandbox dry-run.log show the sole unchanged-item rejection repeatedly.

Repair: backed up the claim, repair note and deliveries.log as `.maint-NA-finite-immersion-1792661099.bak`,
then ran `tools/claim.py done NA lem-sf-finite-immersion-constructibility-interval` under coord/.merge.lock with a
maintenance note. This deletes the obsolete claim and appends its completion
event. The already resolved repair note remains byte-identical. Only this
claim deletion, the new completion log line, and this report are committed;
unrelated pending deliveries.log entries and other work are preserved.

Validation: stage 1 and stage 2 were already complete and the item was absent
from the queue before the repair. The claim is now absent; the node SHA-256
is unchanged (4ebccfed55b5efdd87ac690e2ab2d5514f1ac90e16a9350ecd3ab843ebf4fa34). No mathematics,
Lean source, dispatcher state/counters, launcher code, review service or landing
tools were changed. No compiler, lake build or process signal was used.

Next worker: this stage-1 assignment is superseded; retain Q08's split and N8's
binding. Do not manufacture a node diff or repeat delivery. Work on this stage
requires a newly released stage-1 repair that identifies an actual defect.

Launcher-owned follow-up: dispatch_all.py currently restarts off-queue held
stage-1/2 claims using their saved stage. Its owner should reconcile these
against live completion and released repair state when recovering claims.
No launcher change is required to clear this item's now-closed claim, and no
failure-based stop, cap, throttle, admission restriction or pause is proposed.
