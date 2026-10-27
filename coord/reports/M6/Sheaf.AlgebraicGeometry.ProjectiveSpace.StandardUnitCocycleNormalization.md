## What changed

The target theorem now has a complete Lean proof that combines two strictly
smaller intermediate statements. It applies the off-diagonal normalization for
pairwise distinct indices, applies the diagonal completion statement, and splits
on equality of the two indices. The target DAG node records this revised proof
route. Two new statement modules were added under
`Sheaf.AlgebraicGeometry.ProjectiveSpace`.

## Proved and sorry left

Closed the `sorry` in
`AlgebraicGeometry.ProjectiveSpace.exists_standardUnitCocycle_normalization`.
The two genuinely smaller intermediate statements remain `sorry`:

- `AlgebraicGeometry.ProjectiveSpace.exists_standardUnitCocycle_normalization_offDiagonal`
  isolates the Laurent-polynomial classification and normalization for `i ≠ j`.
- `AlgebraicGeometry.ProjectiveSpace.standardUnitCocycle_diagonal_normalization`
  isolates the repeated-index and cancellation argument extending the equation to
  `i = j`.

Thus one hole was closed and two lower holes were split off.

## No longer needed

The target proof no longer imports or directly cites any previously planned
proof module beyond `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`.
The polynomial-ring and Laurent-polynomial nodes remain needed by the new
off-diagonal proof statement, and the transition-cocycle node remains needed by
the diagonal statement. No imported declaration was pruned.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the pairwise-distinct Laurent calculation and the
repeated-index diagonal completion into one unproved theorem. The available
library declarations do not provide the higher-dimensional Laurent-unit
classification, so the bundled proof could not be completed directly. The DAG
has therefore been refined into the two proper substatements above; the target
statement and all of its binders are unchanged.

## New nodes

`lem-sfb-projective-standard-unit-cocycle-off-diagonal` states the distinct-index
part and records the Laurent-polynomial source and searches. Its Lean declaration
is `exists_standardUnitCocycle_normalization_offDiagonal`.

`lem-sfb-projective-standard-unit-cocycle-diagonal` states the repeated-index
completion from the off-diagonal equations and records the cocycle/cancellation
source and searches. Its Lean declaration is
`standardUnitCocycle_diagonal_normalization`.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
