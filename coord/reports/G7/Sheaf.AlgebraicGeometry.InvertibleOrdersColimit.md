## What changed

Completed `AlgebraicGeometry.Scheme.isTorsionEtaleSheafOfFieldInvertibleOrder_iff_isIso_comparison` in `lean/Sheaf/AlgebraicGeometry/InvertibleOrdersColimit.lean`. Two proved private helpers establish filteredness of the invertible positive-integer index and characterize the comparison after applying an additive functor preserving finite limits and colimits. Apply that criterion to geometric stalks, transport along `uliftSheafFiberIso`, and use the existing conservative-family theorem. All public signatures and definitions are unchanged. Added the proof import `Mathlib.Algebra.Category.Grp.FilteredColimits`.

The module compiled through `lcompile.py` in 9 seconds. The delivery dry run compiled the declarations with its axiom probe and passed preflight. The node records the actual proof route; no new node or change record is needed.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.Scheme.isTorsionEtaleSheafOfFieldInvertibleOrder_iff_isIso_comparison` (node `lem-kun-invertible-orders-colimit`). Proved both private helpers, `invertibleTorsionIndex_filtered` and `invertibleTorsion_map_iff`. Zero holes remain in the item and zero holes were added elsewhere: this is a proof, with no split-off statements.

## No longer needed

Removed these proof-only imports and corresponding proof-dependency uses:

- `Sheaf.AlgebraicGeometry.TorsionFilteredUnion`, node `lemma-weil-pbc-torsion-filtered-union`: the restricted comparison is handled directly; the unrestricted torsion theorem is unnecessary.
- `WeilConjectures.AlgebraicGeometry.GeometricStalkColimits`, node `lem-kun-stalks-commute-colimits`: its separate statement uses integer-module coefficients; Mathlib's skyscraper adjunction supplies colimit preservation directly for the abelian-group stalks used here.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: use Mathlib's `Point.sheafFiber` realization of the same stalk definition. The node `def-weil-pbc-geometric-stalks` remains recorded, with its existing Mathlib match.

No other node dependency is pruned. In particular the Mathlib finite-limit preservation clause of `prop-weil-pbc-geometric-stalks-exact` and abelian-sheaf colimit existence remain used. The hypothesis `hF` is preserved even though the stronger stalkwise invertible-annihilator predicate makes it unnecessary in the proof. The unit has no realized proof steps, and its statement and route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The initial generic-functor proof needed explicit smallest-colimit and filtered-colimit instances before applying `Concrete.isColimit_exists_rep`; these are now supplied. The original DAG used an unnecessary unrestricted torsion-colimit detour and a separate stalk-colimit theorem whose recorded coefficients differ from this module's. The completed proof uses existing Mathlib APIs directly, with no statement or definition repair.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
