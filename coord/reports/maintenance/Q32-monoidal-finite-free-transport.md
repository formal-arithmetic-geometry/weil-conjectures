# Q32 finite-free transport: superseded repair assignment

The repeated failures of lem-sfb-monoidal-finite-free-transport@424048e07 are a stale
stage-1 assignment, not a mathematical defect or a provider failure.

The long-proof re-split request was committed at 05:05 UTC in 22cdafb789e. G4 then
landed the completed theorem at 06:11 UTC in 98a804da515, landing
20261021T061140-L-1722057. That landing replaced the 3590-character proof with four
elementary steps totaling 1673 characters and recorded reviewed_proof.result=pass.
The independent return of Q32 head 424048e0767 at 08:55 UTC accepts the mathematics
but rejects replacing this completed route with a new unsplit coordinate node.
It explicitly requests resolution or retirement of the repair note.

The note remained state=released, which dag_queue.stage1_completed deliberately
treats as reopening even a completed node. The Q32 claim, returned delivery branch
and return entry therefore kept the dispatcher issuing repair prompts. The local
item route note compounded the problem by calling re-splitting despite closure
deliberate. Workers could not repair the certificate mismatch: deliver.py correctly
overlays only split-owned fields and preserves reviewed_proof from live. A passing
dry run does not resolve that independent review objection.

The maintenance resolution marks only the obsolete repair note resolved, preserving
its original request and adding dated evidence. The exact superseded Q32
packet was retired with tools/retire_stage1.py retire_completed, preserving its full Git
head at refs/superseded/Q32/lem-sfb-monoidal-finite-free-transport/424048e07679162550cbc3a71eae10e44a713f1a
and removing its stale return and claim. No DAG node, Lean source or review
certificate needs changing. The local route note is corrected to this disposition.

Validation: SHEAF_GROUP=maint-Q32-finite-free SHEAF_FILE_TIMEOUT=60
tools/lean_file.sh lean/Sheaf/CategoryTheory/MonoidalFiniteFreeTransport.lean exited
0 and printed Compiled in 3.2 s. The source exactly matches the G4 landing. Check
stage1_completed=true, stage1_repair_owed=false, no Q32 claim/return/delivery branch,
and preservation of the archived head after retirement.

Next worker: this stage-1 task is complete. Keep the live Lean-matching proof and
its reviewed_proof pass. The retained sandbox is historical evidence, not an
outstanding delivery. Do not push its coordinate-node split unless a fresh
maintainer decision explicitly reopens the item and reconciles the review state.
The maintenance backup directory is
/home/ubuntu/weil-maintenance-bak/Q32-monoidal-finite-free-transport-1792579138/.

Final server commits:
- 36a171c9d26cab0f1d29899e0625a5588cfa9afc: resolve the stale note and add this report.
- 7a6c1dd2194942a165440d2ce723d0f2963a01c3: preserve three pending operational
  delivery-log entries in a separate bookkeeping commit so the existing retirement
  helper can run against a clean log.
- 5f0abd649a037adc23f639711340ddce88e53a81: retire the exact superseded packet;
  update coord/returns/Q32.md, coord/claims/lem-sfb-monoidal-finite-free-transport.lock,
  coord/deliveries.log and coord/ledger.md, and archive/delete the delivery ref.

All post-repair assertions passed: repair resolved; no stage-1 repair owed;
stage1_completed=true for both the local and queue node; claim.node_finished=true;
no claim, open Q32 return, delivery branch or queue row; archived head exact;
node/source SHA256 unchanged; reviewed_proof still pass for the G4 landing; no new
coordinate node in live. The dispatcher reaped its last worker at 10:55:04 UTC;
subsequent observation found no running, pending or handoff state for this item.
This maintenance session killed no processes.

Existing-file backups: the task backup directory above contains the original note,
pending delivery-log snapshot and this report's earlier version. The retirement
helper's four backups in /home/ubuntu/weil-retire-bak/ have suffix
.retire-stage1-1792579952441155497.bak. The local route-note original has suffix
.maint-Q32-1792579138.bak.

Launcher-owner follow-up: the final already-running worker still reported that
preflight admits the superseded split after the assignment was resolved. Harden
the stage-1 delivery/preflight path to return completion for a completed live item
without a released repair request, and check the current claim before a push.
Keep review-certificate ownership intact. This is a remaining defense against
manual stale submissions; the repaired record/claim/return state already removes
this item from dispatch. No protected launcher, review or landing code was edited.
