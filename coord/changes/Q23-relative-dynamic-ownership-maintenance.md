# Q23 relative dynamic ownership maintenance

The independent return on 97753ddfde39 accepts the item mathematics but requires
F1: shared definitions must belong to a definition node, with an added dependency
from Q27's RelativeDynamicSubgroups. F2 requires preserving Q27's landed record.
The repaired worker packet does both, but deliver2.py drops dependency stmt_deps
changes. The server stage2_delivery.py reader also forbids that field change;
nt_preflight2.graph_findings and landing apply only the dependency's lean record.
Thus a wrapper-only fix would remain incomplete. These tools were not changed.

This maintenance commits the mechanical prerequisite extraction on the base.
Ten definition bodies compare verbatim with Q27's published source; the rest of
that module is identical after removing those blocks and adding the public import.
Its node preserves Q27 attribution, all existing dependencies, mathematical fields
and review records, adding only the new definition edge and updating declaration
ownership and lean.note. The new definition module/node reuse the retained Q23
repair. No item theorem or item Lean record is landed by this maintenance.

Incremental DAG checks, including global reach/unit effects, passed. Compile
commands use tools/lean_file.sh sequentially with SHEAF_FILE_TIMEOUT=60 and
SHEAF_GROUP=M-Q23-maint. No lake build was run. Import-pruning checks also pass.
Landing record: 20261024T195752-M-Q23-maint-2155163

lean/Sheaf/AlgebraicGeometry/RelativeDynamicAttractionData.lean:
Compiled in 4.1 s

lean/Sheaf/AlgebraicGeometry/GroupScheme/RelativeDynamicSubgroups.lean:
Compiled in 6.4 s

lean/.sandbox/M-Q23-maint/RelativeDynamicAttractingSubgroup.lean:
Compiled in 2.2 s




Next worker: fetch current sheaf-dag and rerun deliver2.py Q23
lem-sfb-relative-dynamic-attracting-subgroup --no-push. The prerequisite files now
match the base, so the required edge is retained without changing dependency
metadata in the delivery. Keep the six item statements, including zeroSection at
zero, and preserve Q27's ownership. Synchronize prerequisite node copies with the
base or omit the unchanged prerequisite files; keep the item node and module.
The old repeated wrapper-refusal notes are superseded. Deliver the remaining item
normally for independent review; this maintenance is not that review.

Backups are adjacent .maint-Q23-1792870465.bak files, with ABSENT markers for new
paths. Protected launcher, review, preflight and landing tools were not edited.
If cross-node stmt_deps edits are to become worker-deliverable generally, their
tool owners must update packaging, server ownership validation, effective-graph
simulation and landing application together, preserving dependency additions and
provenance. No such tool change is needed for this repaired item.
