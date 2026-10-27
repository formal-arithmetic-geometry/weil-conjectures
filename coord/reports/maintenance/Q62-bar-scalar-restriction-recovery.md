# Q62 scalar-restriction delivery recovery, 2026-10-25

The returned item lem-trf-bar-scalar-restriction-coherence was delivered successfully
at 9debdfb2a5e6c5051ec8cf81991c661c1bbfaee5 on
refs/heads/deliver/Q62/lem-trf-bar-scalar-restriction-coherence. Independent review
remains pending; this maintenance record does not approve the mathematical item.

## Cause

The 43 counted failures were a deterministic ownership/scope mismatch. The H2
return on b5545c21537e required a definition node owning the presheaf bar data in
its own module, plus an edge from the existing existence-theorem node to that
owner. The retained Q62 packet tried to update the dependency theorem's stmt_deps.
The delivery wrapper deliberately omitted that field (deliver2.py line 141),
printing "stmt_deps of a dependency node may not change; not delivered" while the
incomplete candidate passed compilation and preflight. Repeating the same packet
could not add the reviewer-required edge. The old sandbox also associated the new
definition owner with the old mixed theorem module rather than a separate module.

## Resolution and verification

Shared maintenance for the identical Q34 H2 return already landed the proper
extraction in a39f1804b8b5e64ae33c9f5b1c292f2e8cf2ba3f. That commit adds
Sheaf.CategoryTheory.PresheafBarResolutionData and its definition node, adds the
required theorem dependency edge, and retains exists_resolution in the original
PresheafBarResolution module, which publicly imports the new definition module.
Its definitions preserve all 26 names and formulas; the existence theorem and
complete proof docstring are byte-identical. The new definition module has no
sorry. Both extracted modules were compiled separately using tools/lean_file.sh
with 60 second limits (32.0 and 10.4 seconds in the shared maintenance landing).

The already-running Q62 worker then rebased its retained packet: it imports the
landed definition module directly, cites def-trf-presheaf-bar-resolution-data,
and removes the obsolete definition/theorem node copies. Its H4 repair imports
Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact and deletes the two duplicate
sorried exactness instances and their lean.declarations entries. The item statement,
proof plan and proof dependencies are unchanged; the existence theorem remains
a proof dependency only. No mathematical proof was attempted by maintenance.

The worker compiled the revised module, passed the normal dry run at 679534cee77,
and delivered 9debdfb2a5e6c5051ec8cf81991c661c1bbfaee5 after another successful
server compilation and preflight. The delivery changes exactly the item node,
lean/Sheaf/CategoryTheory/BarScalarRestrictionCoherence.lean, and its Q62 worker
report. The server branch and packet contents were independently verified.

Q62 maintenance adds the dispatcher-consumed brief at
/home/ubuntu/weil-launcher-all/batch2/route-notes/lem-trf-bar-scalar-restriction-coherence.md,
with adjacent .bak snapshots, and this server record. This file is committed under
coord/.merge.lock with SHEAF_LEAD=L-only and Bin Wu's specified identity. A .bak
snapshot is retained in local/maintenance/Q62-scalar-recovery-20261025/backups/.
The upstream extraction's backups are in
local/maintenance/Q34-ownership-20261025/backups/.

## Next worker

Await independent review of 9debdfb2a5e. If returned, rebase on current main and
address the new review. Keep the definition node in stmt_deps and import
PresheafBarResolutionData. Do not restore superseded shared-node copies or the
duplicate scalar exactness instances. Historical BLOCKED notes no longer describe
the present packet. No protected dispatcher, admission, preflight, review or
landing tool was edited, and no throttle, concurrency limit or pause was added.
