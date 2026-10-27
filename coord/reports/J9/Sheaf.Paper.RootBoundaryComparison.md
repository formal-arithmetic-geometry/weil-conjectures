## What changed

Filled the two theorem proofs in `Sheaf.Paper.RootBoundaryComparison`.
`puncture_square` reassociates the composite and applies the second-projection
identity for the actual pullback lift. `testMap_projection` applies that identity
directly. Both use Mathlib's `CategoryTheory.Limits.pullback.lift_snd`, already
available through the existing imports. All signatures, definitions, docstrings
and imports are unchanged. The arguments apply without restrictions on the
number of coordinates, the parameter profinite set or the stratum.

Validation uses the prescribed `lcompile.py` single-file compiler and the
delivery preflight, which also checks the compiled declarations and their axioms.

## Proved and sorry left

Closed 2 of 2 holes, both attached to
`def-sfb-root-boundary-comparison`:

- `AlgebraicGeometry.ProEtale.RootBoundary.puncture_square`.
- `AlgebraicGeometry.ProEtale.RootBoundary.testMap_projection`.

No sorry remains in the item. No holes were added and no results were split off.
These are proofs, not a decomposition into new unfinished statements.

## No longer needed

None. No imports, nodes or modules were removed. The existing public imports
supply the unchanged definitions and statements of the comparison interface;
no proof-dependency imports were added. Neither proof uses an unfinished theorem
from the project.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The node is a definition node, with empty proof
and proof_deps fields, that also owns these two elementary auxiliary theorems.
Their existing docstrings already describe exactly the proofs supplied here,
so the node and the unit route need no change. There is no current return or
rework entry for this item.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
