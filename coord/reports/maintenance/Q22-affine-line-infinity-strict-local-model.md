# Q22 maintenance: affine-line infinity strict-local model

The recent NOANSWER attempts for lem-sc-affine-line-infinity-strict-local-model
ended with terminal Codex HTTP 429 errors. Attempts 1792195293 through
1792197005 all recorded exceeded retry limit, last status: 429 Too Many Requests.
This is a model-service failure, not evidence that the mathematical statement
is defective. Concurrent maintenance is installing shared provider admission
and worker transport recovery; this repair does not overwrite those changes.

Earlier author 1792191111 returned READY. Reader 1792192571 compiled and passed
server preflight at 1391aefe2c, then used its remaining budget in repeated
worktree, Q22 delivery-lock and fetch waits. The retained sandbox already has
one consumer module, an existing-declaration dependency repair, and the reader's
report. No delivery branch reached the server. The module was compiled again
by maintenance through deliver2.py's per-file 60-second server wrapper, with
clean consumer and existing-declaration probe checks.

Maintenance reproduced the queue failure: after reaching worktree admission,
deliver2.py had to wait for an unrelated Q22 delivery and then join the entire
capacity queue again. Stage 1 already locks by group and item, but stage 2 still
locked by group alone. The stage-2 allocator now uses group=f"{g}--{item}".
Same-item attempts still serialize; different Q22 items can progress in their
separate worktrees. Global worktree and compile limits remain in force.

Changed files: tools/launcher/deliver2.py,
tools/launcher/validate_delivery_locks.py, tools/launcher/README.md;
new test tools/launcher/test_stage2_delivery_locks.py;
new route note tools/launcher/route-notes/lem-sc-affine-line-infinity-strict-local-model.md;
this maintenance report. Existing files have sibling
.maint-Q22-strict-local-1792197002.bak backups. The repair is committed as Bin Wu
with SHEAF_LEAD=L-only under coord/.merge.lock. Only these paths are committed.
No Lean source, node mathematics, failure counters or live worker were changed.

Next worker: preserve the existing package, run deliver2.py --no-push, then
answer READY promptly on success. A fresh independent reader must recheck
current files and deliver; the older reader section cannot certify later edits.
The retained module supplies locality explicitly using
AlgebraicGeometry.strictHenselizationLocalStructure from
Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility. Do not reintroduce
the removed duplicate local-structure module. Follow normal stage-2 review.
The full maintenance result and final dry-run outcome are recorded in REPORT.md
in the launcher's Q22 maintenance working directory.

Maintenance final validation: repaired deliver2.py --no-push passed compilation
and server preflight at candidate f6fd3b3bbd, with exactly the four intended files.
Nothing was pushed. The full output is evidence/dry-run.log in the launcher
maintenance directory. Both lock regressions also passed on the server.
