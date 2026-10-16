# Maintenance: derived enriched Yoneda stage-2 scheduling

The repeated NQ stage-2 blocks were caused by omitted statement dependencies.
`lem-coef-derived-enriched-yoneda` names the enhanced localization of right dg
modules and derived dg functor/transformation categories in its statement.
The existing owning nodes `lem-coef-dg-module-projective-resolution` and
`lem-coef-dg-quasifunctor-invariance` were listed only in `proof_deps`; neither
has a usable Lean declaration. The bottom-up queue consequently offered this
consumer before its required interfaces were stated.

Maintenance adds both existing nodes to `stmt_deps`, preserving `proof_deps`,
the statement, proof, source, and reviews. The complete dependency-edge set is
unchanged, so this classification correction cannot introduce a new cycle.
The authoritative DAG is `/home/ubuntu/weil-conjectures-sheaf/dag/nodes`, as
configured by the side project's `SHEAF_DAG`; the same edit is applied to the
side snapshot so synchronization and workers agree. Both edits are committed
under their repository's merge lock, with sibling `.maint-NQ-1792141173.bak`
backups. No Lean file, compiler setting, tool, brief or retry limit is changed.

The premature NQ claim is released through the normal claim tool after queue
regeneration, with a non-abandonment reason. This is dependency ordering, not
giving up because of the failure count. The prerequisite tasks/deliveries
remain available to the normal pipeline. The target becomes stage-2 eligible
again after both prerequisite interfaces are stated and their own statement
dependencies are grounded.

Next worker: use the current node and the prerequisite declarations/imports
when the queue offers it again. Do not duplicate these foundations or replace
enhanced mapping complexes/coherent transformations by ordinary homotopy
categories. The retained NQ sandbox has searches and a diagnostic report but
no faithful target Lean module. The first historical run incorrectly treated
the stage-1 NE merge as completion of the stage-2 task; later workers correctly
diagnosed the missing interfaces. A stage-1 delivery is not a Lean statement.

Validation uses the production `dag_queue.Dag.stage2()` on old and corrected
records and checks eventual eligibility with simulated prerequisite
declarations in memory only. No mathematical construction or theorem is
supplied by maintenance. No Lean compilation is needed for JSON-only edits.
Full operational evidence and final commit ids are in the launcher's
`maint/NQ-lem-coef-derived-enriched-yoneda-1792141173/REPORT.md`.
