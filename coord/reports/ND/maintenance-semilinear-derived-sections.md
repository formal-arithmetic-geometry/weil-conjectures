# Maintenance: lem-coef-semilinear-derived-sections

2026-10-16, ND maintenance run 1792136373.

Cause: this consumer explicitly uses enhanced differential graded localization and homotopy coherent sections. Existing nodes lem-coef-dg-derived-quillen-calculus and lem-coef-quillen-section-rectification introduce these interfaces, but appeared only in proof_deps. Both have no Lean record or Mathlib match. The queue therefore incorrectly considered the consumer ready for stage 2. Workers correctly obeyed the current bottom-up brief, which prohibits stating other DAG nodes in a consumer delivery, and repeatedly reported the same interface gap.

The first failure had a separate trigger: a stage-1 worker started at 07:07:50 UTC and returned READY at 07:21:42 after another group's stage-1 delivery had already landed. The dispatcher read the newly changed queue stage and selected a stage-2 checker against a stage-1 sandbox. The resulting missing-handoff error is not evidence of missing stage-2 files produced by a stage-2 author.

Repair: add the two existing foundations to stmt_deps in the authoritative shared DAG and the side snapshot. Nothing else in the consumer node changes. Keep all proof dependencies and all mathematical statement, proof, and review fields. The full dependency-edge set is unchanged because these edges were already proof dependencies, so no new cycle can be introduced.

Authoritative commit: weil-conjectures-sheaf/sheaf-dag ee4088234f, under coord/.merge.lock as Bin Wu. Matching node path in both repositories: dag/nodes/sec-six-functors/lem-coef-semilinear-derived-sections.json. Each original is preserved as that path plus .maint-ND-1792136373.bak. The side queue reads SHEAF_DAG=/home/ubuntu/weil-conjectures-sheaf/dag/nodes; correcting only the side snapshot would not repair scheduling and could be overwritten by synchronization.

Validation: running the production dag_queue.Dag.stage2 implementation against the authoritative graph showed the consumer eligible before the fix and ineligible after it. Both foundations remain stage-1 tasks with deliveries awaiting review (NK and NL). The side and authoritative consumer records agree exactly after the edit. No Lean source was changed, no Lean compilation was needed, and no placeholder enhancement or new mathematics was introduced. Queue regeneration and stale claim cleanup are recorded in the maintenance run's REPORT.md. Failure counters remain historical evidence.

Next worker: use the current node from newtargets-dag when the bottom-up queue offers it after both enhanced interfaces are stated. Read and import their owning declarations. Do not substitute ordinary DerivedCategory for the enhanced localization or coherent sections, and do not duplicate the existing foundation nodes in this consumer delivery. lem-coef-sheaf-flat-model is a genuine proof dependency; its theorem need not be proved before the consumer is stated.
