# Maintenance: stale NH stage-1 claim for thm-exc-explicit-preservation

The mathematical split is already accepted. Q34 delivery 1a72e36b560 was landed
at 0c1898060b2 on 2026-10-22 11:04:56 UTC, with passing independent review by
NT-cc-Q34-1a72e36b5. The released stage-1 repair note was resolved by that landing.

The landing snapshot still contained a stage-1 row for this item in coord/queue.tsv
(line 466). At 11:05:26 UTC, NH acquired a fresh claim from that stale queue row;
its first worker started one second later. tools/claim.py deliberately grants listed,
unclaimed items (human decisions recorded in 19a02c3a093 and 13f40e5d647), so changing
that policy would be inappropriate. Once the queue was regenerated this item had no
row, but the NH claim remained. dispatch_all.py Group.server only updates the stored
stage for a numeric queue_stage result; an off-queue '-' leaves the old stage 1 in
place. Group.work then dispatches held, undelivered stage-1 claims again without a
live stage-completion check. This caused repeated correct BLOCKED reports and
unchanged-item preflight failures. It was not a mathematical failure or a preflight
bug. Sixteen counted failures and twenty-one retained NH attempt directories were
present at the start of this maintenance.

Repair: after rechecking the live passing review, resolved repair note, absent queue
row, and absence of any NH delivery branch or open return for this item, release only
NH's obsolete claim using tools/claim.py release, with a plain maintenance reason.
Retain the accepted DAG, Lean module, repair note, and worker sandbox. Back up the
claim, deliveries log, and ledger before writing; the backup directory is recorded
below. Commit this audit and the bookkeeping under coord/.merge.lock as Bin Wu.

Launcher follow-up (protected file; not edited): dispatch_all.py needs to reconcile
held stage-1 claims with the current live completion state instead of retaining an
old stage indefinitely when queue_stage returns no stage. A claim whose stage-1
split is accepted and has no released stage-1 repair, live delivery, or unresolved
return should be retired through the claim protocol; a real later-stage assignment
must use that stage's brief. Queue-generation/landing should publish a current queue
with its completion state to avoid the stale-row interval. The queue's current
listed-item policy and failure-count retry policy must be preserved. No throttle,
concurrency cap, admission limit, or pause is part of this repair.

Next worker: stage 1 is complete. Do not manufacture a node edit or repeat an
unchanged deliver.py dry run. Reopen stage 1 only for an explicit new released
stage-1 repair order. The accepted children are lem-exc-bounded-flat-pullback-test,
lem-exc-unbounded-coefficient-pullback-model, and
lem-exc-finite-quotient-constructible-reduction. The parent already has a Lean
statement in Sheaf.Paper.ExplicitExceptionalPreservation; inspection found three
sorry tokens, so this cleanup makes no claim of completed Lean mathematics. Any
future proof assignment must follow the relevant live queue and dependencies.

Validation: before release, stage1_completed=True, queue_stage=None, repair state
resolved, passing Q34 review present, no NH delivery or return. After release,
confirm the item is absent from NH's held claims, all other NH claims survive, and
an off-queue stage-1 take is refused without creating a claim. No Lean source
changed, so no compilation is required.

Backups: /home/ubuntu/weil-maint-bak/NH-thm-exc-explicit-preservation-20261022T185416Z/*.bak
