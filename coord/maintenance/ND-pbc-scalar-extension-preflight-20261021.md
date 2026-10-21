# ND scalar-extension preflight recovery — 2026-10-21

Maintenance item: prop-weil-pbc-scalar-extension@100b8fa83, stage 1, group ND.

The repeated worker failures came from a stale dependency in
dag/nodes/sec-smooth-purity/def-weil-integral-scalar-extension.json, outside
the worker's authorized delivery files. It cited
lem-weil-integral-constructible-linear for ambient derived-category linearity.
That constructible theorem needs triangulation, which needs completed
coefficient presentation transport, which reaches the scalar-extension
comparison and the definition again. The original component also included
prop-weil-pbc-scalar-extension. Its retained repair removed an unused statement
dependency and reduced the component from six nodes to five; it did not create
the remaining cycle. Exact diagnostic-line comparison in tools/dag_delta.py
then classified that smaller component as an introduced finding.

Concurrent NQ maintenance committed the shared data repair while ND was
independently tracing it:
240d5cea108807d4a3171eedf1310f6504ccca17. It replaces the definition's citation
and stmt_deps entry with lem-weil-linear-abelian-derived-category. The existing
lem-weil-integral-scalar-extension-well-defined already states functor
linearity with this ambient input. No defined object, mathematical clause or
Lean record changes. The original definition is preserved as
dag/nodes/sec-smooth-purity/def-weil-integral-scalar-extension.json.maint-NQ-finite-free-20261021.bak.

ND verification:

- A server-side audit pinned to that commit, using the project's own dependency
  extraction and SCC algorithm, recreates the six-node cycle with the old
  definition and the five-node cycle with that definition plus the ND packet.
  With the repaired definition, neither the item nor the definition belongs to
  a cyclic component, with or without the ND packet. The packet adds no cycles.
  Twelve unrelated cyclic components remain; this is not a global clean-DAG claim.
- The unmodified normal command
  `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py ND prop-weil-pbc-scalar-extension --no-push`
  exited 0: `OK (not pushed) deliver/ND/prop-weil-pbc-scalar-extension at d0407595159: preflight passed`.
  The tool saved the durable stage-1 handoff receipt. A subsequent dispatcher
  worker independently passed preflight at 777bd96c222.
- The parent statement remains identical to the committed item, its assembly
  has 2588 characters, and its four children remain unsplit statement-only nodes.
  The delivery tool validated the existing citations and logged searches.

Next worker: retain the complete existing sandbox under
/home/ubuntu/weil-newtargets-sandbox/ND/prop-weil-pbc-scalar-extension, including
the four extracted nodes, argument handoffs, 32 quotations and authentic search
log. The human's re-split instruction remains valid. Refresh main containing
240d5cea10 and follow the normal dispatcher/independent-reader delivery path.
Old five-node-cycle BLOCKED entries describe the obsolete base. Do not restore
the unused strict-tower definition edge on the parent or redo its mathematics.

ND maintenance changed only this durable server note and local handoff
documentation. It did not push an item delivery or change Lean, dispatcher
state, launcher-owned code, review or landing tools. No compiler was needed
for this citation/record repair. The SCC diagnostic comparison issue is
documented in the ND maintenance REPORT.md for the tools' owner; it was not
patched or bypassed.
