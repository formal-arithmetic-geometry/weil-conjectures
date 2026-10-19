## What changed

Proved `AlgebraicGeometry.closedPoint_iff_of_finiteType_product` in the item module. The proof uses Mathlib's Jacobson-space criterion, closed-point preservation under locally finite type maps, finite morphism stability under pullback, and discreteness of fibres of locally quasi-finite maps. It replaces the unused residue-field tensor argument with a shorter geometric proof. Removed the proof-only imports of `Sheaf.AlgebraicGeometry.ClosedPointField` and `WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`.

## Proved and sorry left

The declaration `AlgebraicGeometry.closedPoint_iff_of_finiteType_product` is proved. No `sorry` remains in the item module, and no new `sorry` was added.

## No longer needed

The proof no longer needs `Sheaf.AlgebraicGeometry.ClosedPointField`, `WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`, or the DAG dependencies `lem-kun-closed-point-field`, `lem-weil-pbc-fibre-product-point-residue-field`, `lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-fibre-product-affine-spectra`, `def-weil-residue-field`, `def-weil-affine-spectrum`, and `def-weil-finite-type-morphism` as proof inputs; the needed notions are supplied directly by Mathlib declarations already present in the statement imports.

## Where the brief, the DAG or earlier work was wrong

The imported blueprint route expanded the affine-cover and residue-field tensor argument unnecessarily for the formal statement. Mathlib already provides a geometric route through finite morphisms and discrete fibres, so those planned dependencies are not needed.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
