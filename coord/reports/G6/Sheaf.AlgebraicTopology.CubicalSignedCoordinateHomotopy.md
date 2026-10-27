## What changed

Proved `IntegralLatticeCubical.signedCoordinateHomotopy` in
`Sheaf.AlgebraicTopology.CubicalSignedCoordinateHomotopy`, preserving every existing
signature, definition, and public import. Added private proof imports for `Abel`, `Ring`,
and `SplitIfs`, and proved private helpers for the signed sums, basis evaluation,
degree transport, and face-sign cancellation.

The proof follows the existing seven-step node plan. Integer induction derives
telescoping from the signed-sum recurrence. On cells containing the selected coordinate,
only its boundary face survives and the recurrence evaluates it. On cells not containing
it, its face telescopes and the other faces cancel term by term, with the sign equality
proved by counting filtered direction sets in the two order cases. Equality of linear
maps follows from their values on the free generators. Cardinality proves the zero
extensions and top-degree vanishing directly.

## Proved and sorry left

Closed the sole existing hole:
`IntegralLatticeCubical.signedCoordinateHomotopy`
(node `lem-sfb-cubical-signed-coordinate-homotopy`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivery.
All private helpers are proved; no intermediate results were split off.
The proof does not use `IntegralLatticeCubical.contraction` or the sibling
`boundary_coordinate_projections` theorem.

## No longer needed

None. No imports, nodes, or modules were removed. The original route and its
`def-weil-pbc-free-module` dependency are retained, realized through the existing
`Finsupp.linearCombination` construction and extensionality on generators.
No additional DAG dependencies are required for the elementary finite calculations.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The supplied plan is valid, including
negative paths, zero paths, top degree, and all integer zero-extension degrees.
The rank-zero coordinate assertions are vacuous because their coordinate index has
type `Fin 0`. The comparison with Stacks Tag 0623 supplies no missing cubical theorem;
the face calculation is proved here as the DAG specifies.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
