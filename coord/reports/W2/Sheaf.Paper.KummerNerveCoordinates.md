## What changed

Completed the two theorem proofs in `Sheaf.Paper.KummerNerveCoordinates`.
`kummerNerveVertex_over` unfolds the vertex and parameterized action, rewrites
by the given over-quotient identity, and applies `Over.w` to the parameter
map. `kummerNerveCoordinateMap_over` is the wide-pullback base projection law
`WidePullback.lift_base` after unfolding the two named constructions.
All declaration signatures, definitions, docstrings and public imports stay
unchanged. No new imports, modules, nodes or interface repairs are needed.
The existing node has no proof steps or proof dependencies to replace; the
proofs implement the arguments already recorded in the theorem docstrings.

The single-file server compile passed without warnings in 8.4 seconds.
Searches through msearch grep and Loogle found `WidePullback.lift_base`;
the local source of that lemma and of `coefficientActionFamily` was read.
The LeanFinder request produced no printed result and supplied no premise.

## Proved and sorry left

Closed both original holes:
- `AlgebraicGeometry.ProEtale.kummerNerveVertex_over`.
- `AlgebraicGeometry.ProEtale.kummerNerveCoordinateMap_over`.

Both declarations belong to `def-sfb-kummer-nerve-coordinates`.
There are zero holes left in the item and zero holes added or split off.
The argument applies to arbitrary degree, including degree zero, and uses
identities of scheme morphisms on the entire parameter object.

## No longer needed

None. No imports, nodes or modules are removed. The existing public imports
support the coordinate definitions, action interface, Cech nerve and bar
powers; no additional proof-dependency imports are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The rework row records an older
quarantine caused by a transitive import; the item source is present in the
current library and its original public imports compile. No quarantine
withdrawal or dependency deletion is needed.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
