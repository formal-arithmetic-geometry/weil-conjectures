## What changed

Filled both theorem proofs in `Sheaf.AlgebraicGeometry.AffinePGLAction`.
`Action.constants_mem` uses naturality of `Scheme.ΓSpecIso` and the triangle
identity for morphisms over `Spec k` to identify evaluation of a constant at
every test point with its pullback from the base. Membership in the intersection
of equalizer subrings follows. `Action.quotientMap_over` uses `Spec.map_comp`
and the defining equation of the restricted coefficient map.

All existing statements, definitions, visibility and imports are preserved.
No new declarations, modules or dependencies were introduced.

## Proved and sorry left

Closed 2 of 2 existing holes:

- `AlgebraicGeometry.AffinePGL.Action.constants_mem`
  (node `def-sfb-affine-pgl-action`).
- `AlgebraicGeometry.AffinePGL.Action.quotientMap_over`
  (node `def-sfb-affine-pgl-action`).

No holes remain in the item; no holes were added or split off.

## No longer needed

None. Both existing public imports support the statements and definitions.
The node has no proof dependencies to prune. The proof uses the existing
Mathlib API directly and keeps the unit route unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The definition node has no proof steps;
the existing theorem docstrings supply the two arguments implemented here.
The constants proof applies to arbitrary test schemes, including nonreduced
and empty ones, and does not require a nonzero matrix rank. The quotient
triangle follows from the actual invariant inclusion and specified constants.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
