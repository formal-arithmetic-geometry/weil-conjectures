# Maintenance handoff: lem-coef-finite-reedy-localization

The repeated stage-2 blocks were caused by an omitted statement dependency. The
item’s conclusion speaks about the homotopy coherent localization and the
infinity category of coherent diagrams, transformations, mapping spaces, and
(co)limit cones. Those notions are owned by `def-cbc-enhanced-diagrams-cones`,
which was absent from `stmt_deps` and remains `unsplit` without a Lean binding
or Mathlib match. Workers correctly stopped under the bottom-up rule; the
failure was premature queue eligibility, not a compiler or permission fault.

Maintenance appended `def-cbc-enhanced-diagrams-cones` to
`dag/nodes/sec-six-functors/lem-coef-finite-reedy-localization.json`, preserving
the statement, proof, proof dependencies, searches, and review metadata. The
same record repair was applied to the authoritative live DAG. Backups with the
suffix `.maint-N5-1792151450.bak` are retained beside both node files.

The active dispatcher already rechecks held stage-2 `stmt_deps`, so after this
record is visible it will retire the stale retry path and will not relaunch the
item while the coherent-definition prerequisite is unstated. The normal queue
will resume the item only after that prerequisite has a reviewed Lean binding.
No Lean source was changed and no mathematical statement was rewritten.
