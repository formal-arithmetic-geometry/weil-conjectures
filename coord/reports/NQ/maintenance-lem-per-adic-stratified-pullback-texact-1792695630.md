# Maintenance: stale NQ stage-1 claim for lem-per-adic-stratified-pullback-texact

Cause: the accepted O1 stage-1 landing 5420d4111ff3a9604810dde20d2b0a94f104b4bb
completed the human re-split order at 2026-10-22 11:12:56 UTC. Independent review
NT-cc-O1-30409ce25 passed after FIX. The live node is split, its repair note is
resolved, and its five-step assembly has 2967 characters with two extracted tasks:
lem-per-integral-pullback-bounds and lem-per-rational-stratum-pullback-models.

That landing snapshot still lists the parent at stage 1 in coord/queue.tsv:724.
NQ's claim was created at 11:13:33 UTC, 37 seconds after the recorded completion;
its first stage-1 worker started at 11:14:05 UTC. tools/claim.py take intentionally
honors listed, unclaimed queue items under the human's 2026-10-22 instruction, so
changing that policy is not the repair. The current queue has no parent row, but
the claim survived. dispatch_all.py Group.server only updates a saved stage when
queue_stage returns 1, 2, or 3; an off-queue '-' retains stage 1. Group.work then
restarts a held, undelivered stage-1 claim without checking live completion.
Sixteen counted failures and 21 retained NQ attempts all ended BLOCKED on this
same dispatch conflict. The stage-1 live-wins rule correctly forbids resplitting.

Repair at 2026-10-22T19:03:10Z: rechecked the live completion predicate, passing O1 review,
resolved repair note, absent queue row, and absence of an NQ delivery or return
for this item. Used tools/claim.py release NQ with a plain maintenance reason to
remove only the obsolete claim. This is completion bookkeeping, not abandonment.
All three other NQ claims survived byte for byte. The node, repair note, and Lean
module also survived byte for byte. The accepted mathematics was not redone.

Validation: stage1_completed=True and node_finished(stage=1)=True;
queue_stage=None; repair state=resolved. After release the claim is absent and
the exact dispatcher claim protocol, take-many --with-stage NQ <item> 1, returns
NO: already completed for stage 1 without recreating a claim. No Lean sources
changed, so no compiler or global build was run. Earlier NK stage-2 rollback in
coord/returns/NK.md and ~/cc1/autoland.log is historical and does not reopen the
accepted O1 stage-1 split or create an NQ repair.

Protected launcher follow-up (not edited): reconcile held stage-1 claims against
live stage1_completed plus repair-note state before scheduling; clear or replace
stale stage data when queue_stage returns no stage. Retire a completed stage-1
claim through the claim protocol only after accounting for live deliveries and
unresolved returns. A later-stage assignment needs that stage's current brief.
Protected landing/queue publication should prevent a completed parent remaining
in a stale stage-1 queue snapshot. Preserve the human's listed-item policy and
failure-count policy. This repair introduces no cap, throttle, admission limit,
or pause. No launcher code, review service, or landing tool was edited.

Next worker: stage 1 is complete. Do not duplicate the accepted split, relabel it
ATTACH, or deliver an unchanged item to satisfy a stale assignment. Stage 1 may
reopen only on a newly released stage-1 repair order. Use the live queue for any
later work. The parent's recorded Lean module is
Sheaf.Paper.AdicStratifiedPullbackInterface; this maintenance makes no claim that
its Lean proof or dependencies are complete. Retain the accepted children and
reviewer FIX that dropped lem-per-pullback-coefficient-descent as a conjunction
of existing nodes.

Backups of every pre-existing changed file: /home/ubuntu/weil-maint-bak/NQ-lem-per-adic-stratified-pullback-texact-20261022T190310Z/coord/**/*.bak.
New audit snapshot: /home/ubuntu/weil-maint-bak/NQ-lem-per-adic-stratified-pullback-texact-20261022T190310Z/coord/reports/NQ/maintenance-lem-per-adic-stratified-pullback-texact-1792695630.md.bak.
The worker's retained sandbox report and dispatcher-state evidence were also
archived locally at /home/ubuntu/weil-maint-bak/NQ-lem-per-adic-stratified-pullback-texact-1792695630/.
