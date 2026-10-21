# H7 normalization dependency restoration

The stage-3 item repeatedly failed the source-availability gate for
Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent. Its stage-2 source
landed in 767efb11e75 (landing 20261021T100703-NZ-4072136-1709), then
bulk rollback d34b31cc566 removed it after a red build of 67889a9512.
Its current DAG Lean attachment survived the rollback. A compiled artifact
remained available, so declaration lookup worked while source validation failed.
The restored supporting modules no longer hold this dependency for rework.

Restored lean/Sheaf/TraceFormula/IsomorphismMultiplicationConeDescent.lean
byte-for-byte from the reviewed stage-2 commit through tools/land.sh.
The declaration, real definitions, original theorem sorry, imports and docstrings
are unchanged. The node already records this exact source and needs no change.
Removed only its obsolete rollback return from coord/returns/NZ.md after the
successful landing, preserving the other returns. No proof of the H7 item is
claimed; its worker sandbox is preserved.

Validation: the recovered source compiled in 30.0 seconds with
SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh, then tools/land.sh performed its
sequential sandbox/library compiles and import-pruning checks. Source-inventory
and cycle checks passed. The six modules named by the rollback build have no
current import dependency path to this module. The normal landing record leaves
global verification to the running pipeline; maintenance started no global build.

Backups: the destination's .maint-H7-1792591542.bak records prior absence;
coord/returns/NZ.md and coord/deliveries.log have copies with that suffix.
This note has a .bak copy. The recovery sandbox has a .lean.bak absence marker.
All application, return reconciliation and commit operations used the merge lock
with SHEAF_LEAD=L-only. No protected launcher or landing tool was edited.

Next worker: refresh against this restoration and retain the H7 packet. The
planned import now has a tracked source; keep the true declared dependencies and
finish the original normalization proof through normal delivery. Old reports
about a missing descent source are obsolete. This restores a stated stage-2
lemma, not a proved lemma; its original named theorem hole remains stage-3 work.
