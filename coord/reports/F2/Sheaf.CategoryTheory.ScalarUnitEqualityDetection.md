## What changed

Proved `CategoryTheory.scalar_unit_equality_detection` in
`Sheaf.CategoryTheory.ScalarUnitEqualityDetection`, following the existing four-step DAG proof.
Unit naturality gives equality after the zeroth cocone leg. Forgetting the assumed
abelian-group colimit gives a colimit of sets; Mathlib's same-stage filtered-colimit
criterion supplies a finite transition where the maps agree. Induction computes that
transition as multiplication by `a ^ n`.

The proof explicitly shrinks filtered-colimit preservation to index universes `(0, 0)`
using `preservesFilteredColimitsOfSize_shrink`, preserving the independent Hom universe.
The scalar-power induction includes `n = 0` and uses no positivity hypothesis on `a`.
Statements, docstrings, definitions and imports are unchanged. The DAG route and its
proof dependencies are unchanged, so no node update is needed.

Validation: `lcompile.py` compiled the module cleanly in 2.1 seconds, without warnings.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.scalar_unit_equality_detection`
(node `lem-sfb-scalar-unit-equality-detection`).

Remaining holes: none. Added holes: none. Split-off statements: none.

## No longer needed

None. Both existing private proof imports are used: filtered-colimit preservation for
abelian groups and same-stage equality detection for filtered colimits of sets.
All four declared DAG dependencies remain used. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The existing statement and proof plan are valid. Mathlib's universe-shrinking
preservation lemma handles the small natural-number indexing category directly.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
