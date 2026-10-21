# AlgebraicGeometry.Scheme.adicDatumModelRestriction

## Reason

The ordinary extension presentation is normalized to reductionChange, which selects the same tensor functor as completedConstantExtension (adicDatumOrdinaryExtension_eq is proved by rfl). The pure tensor section is the same sheafification unit. These are definitional identifications, so no hypothesis or conclusion changes.

The targets and their signatures are unchanged. Target statements using these definitions require the normal stage-2 semantic review after landing. No file under WeilConjectures is changed.

## Old

```lean
def adicDatumModelRestriction {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    (adicDatumModelTower T d M).obj (op n) ≅
      (adicDatumRestriction T (adicDatumProjection T d n)).obj
        (adicDatumModelReduction T d M n) :=
  letI := HasDerivedCategory.standard (adicDatumModules T d)
  letI := HasDerivedCategory.standard
    (completedConstantModules T ((adicLisseRingSystem T d.ideal).obj (op n)))
  letI := (adicDatumRestriction_exact T (adicDatumProjection T d n)).1
  letI := (adicDatumRestriction_exact T (adicDatumProjection T d n)).2
  (completedConstantQ _).mapIso (adicDatumModelComplexRestrictionIso T d M n) ≪≫
    ((SheafOfModules.restrictScalars.{t + 1}
    ((adicLisseForget T).map (adicDatumProjection T d n))).mapDerivedCategoryFactors.app
      (((completedConstantExtension T (adicDatumProjection T d n)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M.complex)).symm
```

## New

```lean
def adicDatumModelRestriction {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    (adicDatumModelTower T d M).obj (op n) ≅
      (adicDatumRestriction T (adicDatumProjection T d n)).obj
        (adicDatumModelReduction T d M n) :=
  letI := HasDerivedCategory.standard (adicDatumModules T d)
  letI := HasDerivedCategory.standard
    (completedConstantModules T ((adicLisseRingSystem T d.ideal).obj (op n)))
  letI := (adicDatumRestriction_exact T (adicDatumProjection T d n)).1
  letI := (adicDatumRestriction_exact T (adicDatumProjection T d n)).2
  (completedConstantQ _).mapIso (adicDatumModelComplexRestrictionIso T d M n) ≪≫
    ((SheafOfModules.restrictScalars.{t + 1}
    ((adicLisseForget T).map (adicDatumProjection T d n))).mapDerivedCategoryFactors.app
      (((reductionChange T (adicDatumProjection T d n)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M.complex)).symm
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.CompletedKoszulReductionRoosTriangle | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.CompletedReconstructionUnitComparison | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.FiniteReductionReconstructionCompleted | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
