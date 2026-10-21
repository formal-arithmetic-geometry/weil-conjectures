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
its original request and adding dated evidence. Retire the exact superseded Q32
packet with tools/retire_stage1.py retire_completed; this preserves the full Git
head at refs/superseded/Q32/lem-sfb-monoidal-finite-free-transport/424048e07679162550cbc3a71eae10e44a713f1a
and removes its stale return and claim. No DAG node, Lean source or review
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
