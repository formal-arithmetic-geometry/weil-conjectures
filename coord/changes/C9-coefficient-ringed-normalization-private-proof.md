# coefficient_ringed_square_normalization

## Reason

Preflight classified the new scoped `variable` and `omit` commands in the
`DerivedCompatibility` section as a change of visible commands. The section contains
only proved private helper theorems, and ends before the existing namespace and
variables. Its category parameters do not occur in any public signature. This record
documents that conservative classification; no definition or statement is repaired.
The private proof imports listed in the report are removed as unnecessary.
The elaboration options apply only while checking this file and add no exported
attributes or instances. All four public construction bodies remain verbatim.

## Old

```lean
theorem coefficient_ringed_square_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X₀ Y₀ : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) :
    (coefficientRingedDirectImageComparison a f₀.left).hom =
        (derivedComapLowerStarIso a f₀.left).inv ∧
    (coefficientRingedPullbackComparison a f₀.left).hom =
        (derivedPullIso a f₀.left).inv ∧
    ∀ (I : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X₀.left) Ab.{u + 1})
        (condensedRingObj S X₀.left)) ℤ) [I.IsKInjective],
      (coefficientRingedSourceResolution a f₀.left I).inv ≫
          (coefficientRingedDirectImageComparison a f₀.left).hom.app (DerivedCategory.Q.obj I) ≫
          (coefficientRingedTargetResolution a f₀.left I).hom =
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (comapLowerStarIso a f₀.left)
            (ComplexShape.up ℤ)).inv.app I) ∧
      (coefficientRingedTargetResolution a f₀.left I).inv ≫
          (derivedComapLowerStarIso a f₀.left).hom.app (DerivedCategory.Q.obj I) ≫
          (coefficientRingedSourceResolution a f₀.left I).hom =
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (comapLowerStarIso a f₀.left)
            (ComplexShape.up ℤ)).hom.app I)
```

## New

```lean
theorem coefficient_ringed_square_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X₀ Y₀ : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) :
    (coefficientRingedDirectImageComparison a f₀.left).hom =
        (derivedComapLowerStarIso a f₀.left).inv ∧
    (coefficientRingedPullbackComparison a f₀.left).hom =
        (derivedPullIso a f₀.left).inv ∧
    ∀ (I : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X₀.left) Ab.{u + 1})
        (condensedRingObj S X₀.left)) ℤ) [I.IsKInjective],
      (coefficientRingedSourceResolution a f₀.left I).inv ≫
          (coefficientRingedDirectImageComparison a f₀.left).hom.app (DerivedCategory.Q.obj I) ≫
          (coefficientRingedTargetResolution a f₀.left I).hom =
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (comapLowerStarIso a f₀.left)
            (ComplexShape.up ℤ)).inv.app I) ∧
      (coefficientRingedTargetResolution a f₀.left I).inv ≫
          (derivedComapLowerStarIso a f₀.left).hom.app (DerivedCategory.Q.obj I) ≫
          (coefficientRingedSourceResolution a f₀.left I).hom =
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (comapLowerStarIso a f₀.left)
            (ComplexShape.up ℤ)).hom.app I)
```

The signature above is unchanged. Its former `sorry` is replaced by the complete
proof from universal right-derived units and the specified conjugate comparisons.

## Users

`tools/downstream.py Sheaf.Paper.CoefficientRingedSquareNormalization --uses
coefficient_ringed_square_normalization` reports zero downstream modules. Searching
all four public construction names also finds only the item itself. No consumer
requires adaptation. The DAG parents and the unit route keep the same statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientRingedSquareNormalization | C9 | One hole proved; unchanged public types and construction bodies; proved private helpers only. |

Target statements and their definitions do not change, so no target-statement
review is reopened. This packet changes no source-library modules.

## Status

landed 20261023T165917-L-2043559 2026-10-23 (merge of deliver/C9/Sheaf.Paper.CoefficientRingedSquareNormalization)
