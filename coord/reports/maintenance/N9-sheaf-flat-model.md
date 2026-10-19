# N9 maintenance: lem-coef-sheaf-flat-model

2026-10-16. Project: `/home/ubuntu/weil-newtargets`; stage 2; dispatcher key
`lem-coef-sheaf-flat-model@new`.

## Cause

The repeated failures were dependency and delivery-handoff faults, before the
item's Lean preflight, rather than failed proofs of the flat-model theorem.

1. The statement says that its enhanced localization is stable, with finite
   homotopy limits/colimits and equivalent homotopy pushout/pullback squares.
   The coherent mapping-space/cone definitions belong to
   `def-cbc-enhanced-diagrams-cones`, but the target's `stmt_deps` omitted this
   definition. Consequently the queue declared the target ready while workers
   correctly reported its missing interface. Proof-only prerequisites do not
   fix a missing statement-definition dependency.
2. The prerequisite already had a prepared definition-only stage-1 split and
   successful dry-run preflight. Its actual delivery stalled on shared-worktree
   capacity and group-delivery locks, then timed out. `deliver.py` and
   `deliver2.py` reserved scarce worktree slots before waiting for a per-group
   lock; multiple deliveries of a group could consume slots while doing no work.
   Stage 2 also reserved its worktree before independent compilation.
3. The authoritative DAG is the server's
   `/home/ubuntu/weil-conjectures-sheaf/dag/nodes` on `sheaf-dag`, as configured by
   `coord/sheaf.env`; the side project's DAG is an overlay. A side-only repaired
   split did not fix the authoritative queue until it was promoted there.

Evidence: dispatcher `run/N9/state.json` notes and worker logs consistently name
this prerequisite. The prerequisite stage-1 run
`run/NP/def-cbc-enhanced-diagrams-cones.1792148125/log.txt` records a passing
preflight; subsequent runs show slot/lock waits. The target's original nine
statement dependencies contain no enhanced-diagram definition. The existing N1
maintenance note describes the same missing interface for two other consumers.

## Changes and server commits

All server commits used `SHEAF_LEAD=L-only`, the appropriate
`coord/.merge.lock`, and author `Bin Wu <844524296@qq.com>`.

- `c38319a095` (live `sheaf-dag`): promoted the prepared, reviewed definition-only
  split at `dag/nodes/sec-smooth-purity/def-cbc-enhanced-diagrams-cones.json`.
  Backup: `<node>.maint-N9-1792151874-live.bak`. This lets the definition proceed
  to stage 2; it does not assert that a Lean interface already exists.
- `e1913fc592` (side `newtargets-dag`): installed the final valid reviewed split.
  Earlier side commits were `b9a1c3c6db`, `f1347b96b1`, and `31df2653ac`.
  The review-metadata write in `f1347b96b1` accidentally appended a literal
  backslash-n and temporarily made that side JSON invalid. I corrected it;
  `e1913fc592` is the final valid split. The intermediate error caused unrelated
  preflights to reject the shared snapshot and is not a claimed original cause.
  Backups are beside the node with `.maint-N9-1792151874*.bak` suffixes.
- `7e1265a660` (live) and `305bed8335` (side): added exactly
  `def-cbc-enhanced-diagrams-cones` to
  `dag/nodes/sec-six-functors/lem-coef-sheaf-flat-model.json:stmt_deps`.
  The statement, proof, proof dependencies and Lean bindings were preserved.
  Backup in each repository: `<node>.maint-N9-1792151874-stmtdep.bak`.
- `55d852ddc6` (side): versioned the corrected delivery wrappers under
  `tools/launcher/deliver.py` and `tools/launcher/deliver2.py`, their pre-change
  `.maint-N9-1792151874.bak` snapshots, and
  `tools/launcher/route-notes/lem-coef-sheaf-flat-model.md`.
  Installed wrappers are `/home/ubuntu/weil-launcher-nt/deliver.py` and
  `deliver2.py`, with backups alongside them. Stage 2 now compiles before
  reserving a worktree. New invocations load the fix; existing invocations
  retain their old code.
  The route note is installed under `/home/ubuntu/weil-launcher-nt/route-notes/`.
- `44765b4105` (side): completed coordinated reservation in
  `tools/launcher/sharedrepo.py` and the two wrappers. The installed helper is
  `/home/ubuntu/weil-launcher-all/sharedrepo.py`, with its original `.bak`.
  A caller waiting on its group holds no slot; if the pool is full, it releases
  the group before sleeping. This also permits older callers that already hold
  slots to finish without a lock-order deadlock. Intermediate wrapper backups
  use `.maint-N9-1792151874-coordinated.bak`. The subprocess regression harness
  is versioned as `tools/launcher/validate_delivery_locks.py`.
- Queue regeneration after the live promotion was committed by the ordinary
  queue writer at `42221b1f5f`. `61a9e049fd` records this maintenance's queue/index
  backups. `6a7b2865ae` was the earlier side index refresh. Generated files are
  `coord/queue.tsv`, `coord/queue.md`, and `coord/blueprint-index.tsv`; retained
  backups use `.maint-N9-1792151874-{reviewqueue,finalqueue,canonicalqueue}.bak`.

Used `sharedrepo.cleanup('weil-newtargets')` once to remove abandoned worktrees
whose recorded owner PIDs had exited. No active worktree was removed and no
process belonging to another session was killed. No failure counter was reset,
no attempt threshold was introduced, and the dispatcher was not restarted.

## Validation and current handoff

- JSON comparison with both target backups confirms that `stmt_deps` is the
  only changed field, with exactly one added edge. A dependency traversal found
  no path from the prerequisite back to the target in either DAG.
- The server's actual `Dag.stage2()` includes the prerequisite and excludes the
  target while that definition lacks a Lean declaration. The regenerated
  published queue likewise lists the prerequisite at stage 2 and omits the
  target. At the final check (21:14 Asia/Shanghai), the last target worker had
  exited naturally, its server claim was absent, and no target worker was
  running. Its 21 counted attempts and diagnostic note were retained. This is
  a real dependency wait, independent of failure counts.
- `validate_delivery_locks.py` exercises both installed wrappers in subprocesses:
  a busy group reserves no slot, and a full slot pool retains no group lock.
  Both cases resume after release, including compatibility with a legacy caller
  already holding a slot. Both wrappers use this coordinated allocator, and all
  three installed Python files pass syntax parsing.
- The normal NP worker started stage 2 at 20:25:58, wrote
  `lean/Sheaf/CategoryTheory/EnhancedDiagramsCones.lean`, and passed sequential
  sandbox/library compilation (60 seconds per file). Its worker dry run passed
  at `04ad4d3388`, and the dispatcher started its independent second reader at
  20:44:30. The second reader's dry run passed at `95e432f6c5`.
- Maintenance reran the prescribed dry run with the existing larger slot-pool
  override; commit `00cb89dc28` compiled and passed the full server preflight,
  including second reading. Output is retained in `prerequisite-preflight.log`.
  An additional maintenance-owned push attempt was cancelled by this maintenance
  while it waited on the group lock; the normal NP reader/delivery was left
  running. No delivery success is claimed for that cancelled attempt.
  No Lean source was written or mathematically modified by this maintenance;
  no `lake build` was run.

The prerequisite's reviewed delivery is still going through its normal delivery
and independent landing pipeline. A compiled sandbox is not a published Lean
binding. This report does not claim that either theorem has been proved or that
the prerequisite is already landed.

## What the next worker should know

Resume the existing N9 sandbox; do not start over. Refresh the shared checkout,
preserve the newly added direct `stmt_deps` edge in the sandbox node, and wait
for the prerequisite's published binding. Its prepared module is
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, whose main declaration is
`SSet.Enhanced.coneCategory` and whose node lists the remaining helpers.
Use the eventual published record and import its module. Do not inline another
node's definition, replace coherent limits with ordinary homotopy-category
limits, or encode missing coherence as arbitrary proposition fields.

The old N9 sandbox node has the old dependency list; rebase it before delivery.
A delivery tool rejecting its dropped dependency is enforcing the repaired
record. Retain proof-only prerequisites for the stage-3 plan; they do not all
need theorem bindings before this statement can be written. Compile changed
Lean files individually through the prescribed wrapper / `tools/lean_file.sh`,
60 seconds each. A queued legacy delivery can still have loaded the old lock
order; preserve its work and let its owner finish naturally.
