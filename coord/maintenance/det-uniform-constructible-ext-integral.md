# det-uniform-constructible-ext-integral: stale stage-2 claim

NX's statement delivery 79289e02f8 was accepted in side-project commit de122df38e,
batch eadb912d10a34694afdcb9449c52b053, promoted at 2026-10-18T05:44:25Z.
The node has lean.module Sheaf.Paper.UniformConstructibleExtIntegral and a passing
reviewed_lean record. NK acquired a stale claim at 05:44:44Z, 19 seconds later.

Cause: tools/claim.py's take and next skipped node_finished whenever queue_stage
was 2. node_finished already has stage-specific logic: a split without Lean is
open in stage 2, while a recorded declaration is finished. The redundant bypass
allowed a stale queue row to reassign the landed item. The dispatcher then kept
restarting its still-held claim even after the row disappeared from queue.tsv.

Repair: apply node_finished in both claim paths, retaining the explicit released
repair handoff exception. Eight new regression tests cover stale take, take-many,
next choosing an unstated successor, ordinary unfinished stage 2, conventions,
Mathlib leaves, released repairs, and stage-1 completion/review withdrawal.
Close only NK's stale claim with claim.py done, after backing up its lock and the
append-only delivery log. This is reconciliation of NX's accepted delivery, not
a second delivery. No statement, node, module, worker brief, or failure counter
needs changing. No processes were killed and no dispatch limits were introduced.

Validation: the regressions reproduced five failure cases on the original code;
the eight new tests and five existing test_claim_handoff tests pass after repair.
A broader 18-test run had 17 passes and one pre-existing test_repair_queue error:
its fake subprocess result lacks stdout in retire_delivery. Re-running that test
against the backed-up original claim.py reproduces the same error.
The existing published module compiles via tools/lean_file.sh in 3.6 seconds,
nice 19, two threads, 60-second limit; scompile.py --source resolves its theorem.

Launcher follow-up (protected code, not edited): dispatch_all.py Group.work should
reconcile already-held, completed stage-2 statements against the current server
node/repair record before launching or relaunching them, preserving active
returns and explicit repair handoffs. This closes a second recovery gap for stale
claims that already exist. It must not depend on failure counts or add delays.

Next worker: stage 2 of this item is complete. Use the published declaration
AlgebraicGeometry.ProEtale.CondensedRing.uniformConstructibleExtIntegral.
Do not duplicate or re-deliver it without a new explicit repair return/handoff.
Backups retained beside tools/claim.py, coord/deliveries.log and the former
coord/claims/det-uniform-constructible-ext-integral.lock, with suffix
.det-uniform-20261018.bak. Existing unrelated work is outside this repair.
