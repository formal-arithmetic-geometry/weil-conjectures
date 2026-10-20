# AlgebraicGeometry.Scheme.affineFree_residueSections_cohomologyLinearEquiv

## Reason

The restored affine residue comparison theorem has `schemeDerivedCategory`,
`moduleRings`, and related derived-category objects in its public signature. Its
public imports already provide the upstream definitions, but the published
artifact still reflected the retired `Sheaf.AlgebraicGeometry.DerivedFiberBetti`
module. Adding the explicit upstream `DerivedCategory` public import makes the
restored module's public interface self-contained and forces recompilation
against the adopted source tree. This is required for the assigned module to
compile after the retirement of the duplicate Sheaf module.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBettiModelResidueMinimality | N3 (same delivery) | Its proof imports the restored comparison theorem; the explicit public import resolves the adopted upstream interface and changes no theorem signature. |

## Status

landed 20261020T235611-L-1194810 2026-10-20 (merge of deliver/N3/Sheaf.AlgebraicGeometry.AffineBettiModelResidueMinimality)
