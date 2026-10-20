# AlgebraicGeometry.schemeDerivedTensorCohomologyVanishes

## Reason

The Sheaf and adopted source modules both declared this exact public name. Importing
TorAmplitudeOpenLocal with ResidueBettiZeroOfTensorVanishing therefore failed with a
Lean environment duplicate-declaration error. Reexport the adopted declaration from the
Sheaf module. Preserve all three old public imports, adding only the adopted module.
The private `adopted_vanishing_eq_original` theorem in TwoTermPerfectTorWindow proves by
`rfl`, for independent universes u and w, that the adopted predicate has the entire old
body. In particular IsKFlatTensor and IsAcyclicTensorKFlat are definitionally equal here.
No definition or signature in WeilConjectures is modified. No target meaning changes.

## Old

```lean
def schemeDerivedTensorCohomologyVanishes (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E) ∧
      IsZero ((CochainComplex.mapBifunctor P
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
        (curriedTensor _)).homology i)
```

## New

The Sheaf path publicly imports
`WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes`, which declares:

```lean
def schemeDerivedTensorCohomologyVanishes (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    CochainComplex.IsKFlatTensor (R := X.sheaf) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E) ∧
      IsZero ((CochainComplex.mapBifunctor P
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
        (curriedTensor _)).homology i)
```

The unchanged public name is thus owned by exactly one module. The node's Lean attachment
points to that source declaration; its statement and mathematical meaning are unchanged.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes --uses
AlgebraicGeometry.schemeDerivedTensorCohomologyVanishes` found the following users.
The similarly named DerivedTensorComplexCohomologyVanishes imports the module but does
not use this predicate; it too is included in the compilation check.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes | unclaimed | Reexport the identical adopted predicate; no hole added. |
| Sheaf.AlgebraicGeometry.AffinePerfectCutSheafRealization | unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.LowestResidueModelWithinOpen | unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.OpenImmersionTensorVanishing | unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.PerfectCutComplexDegreeZero | unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts | unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.ResidueBettiZeroOfTensorVanishing | unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.UniversalLowestFiberRanks | unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | quarantined; unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | quarantined; unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | quarantined; unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.PerfectLowestMatrixClosedLocus | unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel | unclaimed | Same predicate name, type and definitionally equal body; unchanged source compiled against the reexport. |
| Sheaf.AlgebraicGeometry.DerivedTensorComplexCohomologyVanishes | unclaimed | Import-only consumer; unchanged source compiled against the reexport. |
| Sheaf.TraceFormula.TwoTermPerfectTorWindow | G2, new | The proof imports both families and checks the old predicate body by rfl. |

## Status

landed 20261020T233143-L-899803 2026-10-20 (merge of deliver/G2/Sheaf.TraceFormula.TwoTermPerfectDeterminant)
