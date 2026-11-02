/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedTowerRoos
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstruction
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedReductionAdjunction
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedReductionConstructible
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-!
# Normalized coefficient towers and derived-complete integral complexes

Source: blueprint main-20261015, sec-smooth-purity,
`sk-lem-sp-tower/sk-lem-sp-tower-equivalence.md`; Bhatt--Scholze, Lemma 3.5.7
(blueprint: det-sp-normalized-equivalence).

## Main definitions and statements

- `spCompletedReduction`: the existing reduction transported to completed coefficients.
- `spCompletedTotalLimit`: exact scalar forgetting followed by total derived inverse limit.
- `spCompletedTotalProjection`: the resolution-normalized limit projections.
- `SpNormalizedEquivalence`: the adjunction, its isomorphisms, and constructible restriction.
- `sp_normalized_equivalence`: existence of this normalized equivalence data.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- The ambient reduction/total-limit adjunction, its isomorphisms on complete and
normalized objects, and its restriction to the recorded constructible categories.
Exact scalar forgetting is part of the construction, not an additional hypothesis.
Source: blueprint, normalized equivalence; Bhatt--Scholze, Lemma 3.5.7
(blueprint: det-sp-normalized-equivalence). -/
structure SpNormalizedEquivalence (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) where
  /-- Forgetting actions preserves componentwise addition. -/
  [forgetAdditive : (spCompletedStrictTower l E T D).Additive]
  /-- Forgetting actions preserves kernels and finite products. -/
  [forgetLimits : PreservesFiniteLimits (spCompletedStrictTower l E T D)]
  /-- Forgetting actions preserves cokernels and finite coproducts. -/
  [forgetColimits : PreservesFiniteColimits (spCompletedStrictTower l E T D)]
  /-- Total derived limit is exact, with its standard integer shift structure. -/
  [limitShift : (spCompletedTotalLimit l E T D).CommShift ℤ]
  /-- It carries distinguished triangles to distinguished triangles. -/
  limit_triangulated : (spCompletedTotalLimit l E T D).IsTriangulated
  /-- The products in the Roos triangle are products in the derived category. -/
  [products : HasCountableProducts
    (DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))]
  /-- The Roos triangle uses the actual derived strict-tower transitions and the
  K-injective-normalized projections; it chooses no arbitrary lift from a triangle. -/
  roos : ∀ C : spDerivedCoefficientTowers l E T D,
    ∃ δ : (∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) ⟶
        ((spCompletedTotalLimit l E T D).obj C)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ (spDerivedCompletedTransition l E T D n).app C)
        ((spCompletedTotalLimit l E T D).obj C)
        (Pi.lift (fun n : ℕ ↦ (spCompletedTotalProjection l E T D n).app C)) δ
  /-- The ambient adjunction on the ordinary unbounded derived categories. -/
  adjunction : spCompletedReduction l E T D R ⊣ spCompletedTotalLimit l E T D
  /-- No boundedness or constructibility is assumed on a derived-complete object. -/
  unit_isIso : ∀ M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T),
    WeilConjectures.IntegralOnSlice.IsComplete l E T none M →
      IsIso (adjunction.unit.app M)
  /-- No boundedness or constructibility is assumed on a normalized tower. -/
  counit_isIso : ∀ C : spDerivedCoefficientTowers l E T D,
    IsSpNormalizedTower l E T D C → IsIso (adjunction.counit.app C)
  /-- Only the constructible restriction assumes that T is Noetherian. The two
  equalities say that these are precisely the restrictions of reduction and total limit. -/
  restriction : IsNoetherian T →
    ∃ e : WeilConjectures.sfIntegralConstructibleCategory l E T ≌
        spNormalizedConstructibleTorTowerCategory l E T D,
      e.functor ⋙ (spNormalizedConstructibleTorTowers l E T D).ι =
        (WeilConjectures.sfIntegralConstructible l E T).ι ⋙ spCompletedReduction l E T D R ∧
      e.inverse ⋙ (WeilConjectures.sfIntegralConstructible l E T).ι =
        (spNormalizedConstructibleTorTowers l E T D).ι ⋙ spCompletedTotalLimit l E T D

end AlgebraicGeometry.ProEtale
