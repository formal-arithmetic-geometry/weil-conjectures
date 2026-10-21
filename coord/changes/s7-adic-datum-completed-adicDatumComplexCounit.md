# AlgebraicGeometry.Scheme.adicDatumComplexCounit

## Reason

The ordinary extension presentation is normalized to reductionChange, which selects the same tensor functor as completedConstantExtension (adicDatumOrdinaryExtension_eq is proved by rfl). The pure tensor section is the same sheafification unit. These are definitional identifications, so no hypothesis or conclusion changes.

The targets and their signatures are unchanged. Target statements using these definitions require the normal stage-2 semantic review after landing. No file under WeilConjectures is changed.

## Old

```lean
def adicDatumComplexCounit (C : CochainComplex (completedConstantModules T R) ℤ) :
    (adicDatumExtension T φ).obj ((completedConstantQ _).obj C) ⟶
      (completedConstantQ _).obj
        (((completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  (adicDatumExtension T φ).map ((DerivedCategory.quotientCompQhIso _).inv.app C) ≫
    (adicDatumExtensionCounit T φ).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≫
    (adicDatumQh T S).map
      (((completedConstantExtension T φ).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app C) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
```

## New

```lean
def adicDatumComplexCounit (C : CochainComplex (completedConstantModules T R) ℤ) :
    (adicDatumExtension T φ).obj ((completedConstantQ _).obj C) ⟶
      (completedConstantQ _).obj
        (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  (adicDatumExtension T φ).map ((DerivedCategory.quotientCompQhIso _).inv.app C) ≫
    (adicDatumExtensionCounit T φ).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≫
    (adicDatumQh T S).map
      (((reductionChange T φ).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app C) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.ProperBaseChangeFourCorners | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |

| Sheaf.Paper.CompletedFiniteReductionTensorComparison | unclaimed | Uses the same universal complex counit; its three necessary proof-line adaptations are included and compile. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
