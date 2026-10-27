# Closed-row ownership maintenance, 2026-10-24

The returned delivery 19766f6117ab requires a downstream repair of
FiniteClosedCoverResolution. The stage-2 packet reader only admits prerequisite
nodes, so it drops the included downstream cover node and then rejects its module
as ownerless. Adding the cover theorem as a prerequisite would create a cycle.
The same enforced refusal recurred throughout the NR worker retries.

This maintenance prelands the shared portion of the worker's retained repair:
FiniteClosedRowConstructions, FiniteClosedAugmentedRows, their definition nodes,
and the cover module/record refactor. All thirteen moved helper declarations are
verbatim copies of the live declarations, with only their blueprint owner tags
changed. The cover theorem's signature and single sorry are preserved. Its row
structure now extends the common row definition; its row and total predicates
reuse the common predicates. Both definition owners are added to its stmt_deps.

The unused proof import of ClosedRestrictionTotalPullback is deferred until that
statement lands. Its statement is not landed or marked reviewed by this repair.
The next worker should retain the unchanged comparison module and its own node,
use the landed definitions, and remove the now-redundant downstream cover module
and node from its delivery sandbox (after keeping .bak copies). Normal deliver2.py
preflight and independent statement review then apply.

The landing and review tools are unchanged. Per-file compilation uses
tools/lean_file.sh with the standard 60-second limit. Backups accompany every
changed library/node file with suffix .maint-NR-1792836891.bak; empty backups mark
new paths that did not exist before this maintenance.

Validation and environment recovery:

- Normal `deliver2.py NR lem-sfb-closed-restriction-total-pullback --no-push`
  passed: dry-run commit 0f9d6b52237, with only the item node, unchanged comparison
  module and report staged. The next worker also obtained a passing reduced-packet
  dry run at 5e673b80a1b. No ownership-gate override was used.
- The filesystem was full and large DAG cache files regenerated the reclaimed
  space. Generated `local/nodes-cache` now points to the existing tmpfs at
  `/tmp/weil-sheaf-nodes-cache`. The directory/symlink exchange was atomic; no
  writer was stopped and no concurrency setting was changed. Original cache
  bytes are preserved in `.bak` files under
  `/tmp/NR-closed-restriction-maint-1792836891/` with SHA-256 manifests.
  The old disk directory is `local/nodes-cache.maint-NR-1792836891.bak`.
- `lean/WeilConjectures/Mathlib/LinearAlgebra/Matrix/Rank.lean` had been truncated
  to 4096 bytes during the full-disk incident. Its partial bytes are preserved as
  `.maint-NR-1792836891.bak`. Restoring the committed 7942-byte file and compiling
  it with tools/lean_file.sh (5.3 s) repaired the import scanner crash. This source
  recovery has no diff against HEAD.
- The original landing ownership limitation remains in the protected tool:
  tools/stage2_delivery.py read_delivery excludes a downstream existing node
  before assigning module owners. A future tool change should recognize an
  independently authorized downstream lean-only consumer repair without adding
  a reverse dependency. No review or landing tool was modified here.
- This cache is disposable. After a server reboot, recreate its tmpfs destination
  (`mkdir -p /tmp/weil-sheaf-nodes-cache`) before using the existing symlink, or
  have the launcher owner replace this placement with managed cache lifecycle
  handling. No service, launcher script or system configuration was edited.
