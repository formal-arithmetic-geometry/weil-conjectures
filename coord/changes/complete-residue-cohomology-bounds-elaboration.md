# WeilConjectures.complete_residue_cohomology_bounds: proof elaboration environment

## Reason

The new proof must keep the site at universe u and module coefficients at u+1. Competing specialized sheafification and derived-category instances caused incompatible universe inference in early elaboration attempts. The setup selects the existing canonical witnesses at those sizes and the standard derived-category realization. Its three private witness wrappers are registered only locally. Private helpers use additional universe names and category namespaces, and completed-coefficient/scalar-extension witnesses are locally irreducible to avoid expanding their full constructions in routine equality checks.

The delivery checker classifies changes to open/universe/attribute commands as changes to what importers see and requires this record. This is an elaboration-environment record: no existing declaration signature, definition body, target hypothesis or conclusion changes. The theorem signature below is identical in Old and New. No source-library file or consumer is edited. The independent reader should check the command scope as well as the proof.

## Old

Original module setup, verbatim:

```lean
@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures
```

Original public signature, verbatim:

```lean
theorem complete_residue_cohomology_bounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [CompactSpace X]
    (K : @DerivedCategory (integralTowerModules.{u, u} l E X) _
      (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
        (completedIntegralCoefficientSheafUnrestricted l E X)
        (integralCoefficientAbSheafify.{u, u} X)
        (integralCoefficientAbLocallyBijective.{u, u} X))
      (integralTowerHasDerivedCategory.{u, u} l E X))
    (_hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X K)
    (a b : ℤ) (_hab : a ≤ b)
    (_hTor : ∀ V : X.ProEt,
      HasProEtaleTorAmplitude.{u} V.left (Padic.coefficientExtensionRing l E 1)
        ((proEtaleRingDerivedPullback.{u} V.hom
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
          (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
          (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso.{u}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
            ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)) a b) :
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((@DerivedCategory.homologyFunctor (integralTowerModules.{u, u} l E X) _
        (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
          (completedIntegralCoefficientSheafUnrestricted l E X)
          (integralCoefficientAbSheafify.{u, u} X)
          (integralCoefficientAbLocallyBijective.{u, u} X))
        (integralTowerHasDerivedCategory.{u, u} l E X) j).obj K)
```

## New

New module setup, verbatim (the three helper instances are private and local and their instance registration is local):

```lean
@[expose] public section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [-instance] integralOperationsAbLocallyBijective integralOperationsAbSheafify
  integralOperationsCommHasDerivedCategory
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  integralReductionSiteEssentiallySmall
  integralReductionSourceHasDerivedCategory integralReductionTargetHasDerivedCategory
  integralCompletedRingHasDerivedCategory scalarReductionSourceDerived
  scalarReductionTargetDerived integralTowerHasDerivedCategory

attribute [local instance 5000] HasDerivedCategory.standard

private noncomputable local instance fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X

private noncomputable local instance fixedLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X

private local instance fixedSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u} _

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence integralReductionExistence
  integralReductionDerivedExistence
```

Public signature, verbatim:

```lean
theorem complete_residue_cohomology_bounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [CompactSpace X]
    (K : @DerivedCategory (integralTowerModules.{u, u} l E X) _
      (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
        (completedIntegralCoefficientSheafUnrestricted l E X)
        (integralCoefficientAbSheafify.{u, u} X)
        (integralCoefficientAbLocallyBijective.{u, u} X))
      (integralTowerHasDerivedCategory.{u, u} l E X))
    (_hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X K)
    (a b : ℤ) (_hab : a ≤ b)
    (_hTor : ∀ V : X.ProEt,
      HasProEtaleTorAmplitude.{u} V.left (Padic.coefficientExtensionRing l E 1)
        ((proEtaleRingDerivedPullback.{u} V.hom
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
          (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
          (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso.{u}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
            ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)) a b) :
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((@DerivedCategory.homologyFunctor (integralTowerModules.{u, u} l E X) _
        (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
          (completedIntegralCoefficientSheafUnrestricted l E X)
          (integralCoefficientAbSheafify.{u, u} X)
          (integralCoefficientAbLocallyBijective.{u, u} X))
        (integralTowerHasDerivedCategory.{u, u} l E X) j).obj K)
```

## Users

`tools/downstream.py Sheaf.Paper.CompleteResidueCohomologyBounds --uses complete_residue_cohomology_bounds` lists ten downstream importers and finds no actual use outside the item itself. The rows include all ten, including parents whose proof remains unfinished.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompleteResidueCohomologyBounds` | X3 | Proof completed; signature verbatim; local elaboration setup. |
| `Sheaf.Paper.FieldStageOrdinaryRealization` | unclaimed | No edit; theorem signature and meaning unchanged. Downstream importer only; no actual textual theorem use. |
| `Sheaf.Paper.FieldTorAmplitude` | unclaimed | No edit; theorem signature and meaning unchanged. Downstream importer only; no actual textual theorem use. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | No edit; theorem signature and meaning unchanged. Downstream importer only; no actual textual theorem use. |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | P5 | No edit; theorem signature and meaning unchanged. Downstream importer only; no actual textual theorem use. |
| `Sheaf.Paper.TateTwistLisseLine` | unclaimed | No edit; theorem signature and meaning unchanged. Downstream importer only; no actual textual theorem use. |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | G8 | No edit; theorem signature and meaning unchanged. Downstream importer only; no actual textual theorem use. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | No edit; theorem signature and meaning unchanged. Downstream importer only; no actual textual theorem use. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | No edit; theorem signature and meaning unchanged. Downstream importer only; no actual textual theorem use. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | No edit; theorem signature and meaning unchanged. Downstream importer only; no actual textual theorem use. |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | unclaimed | No edit; theorem signature and meaning unchanged. Downstream importer only; no actual textual theorem use. |

## Status

landed 20261021T120931-L-4006900 2026-10-21 (merge of deliver/X3/Sheaf.Paper.CompleteResidueCohomologyBounds)
