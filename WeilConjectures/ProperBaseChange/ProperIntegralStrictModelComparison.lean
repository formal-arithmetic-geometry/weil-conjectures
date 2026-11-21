/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProperIntegralOrdinaryData
import WeilConjectures.ProperBaseChange.IntegralPullbackIdentificationExists
import WeilConjectures.ProperBaseChange.IntegralStrictModelMatchingExists
import WeilConjectures.ProperBaseChange.IntegralCompletionMatchingOnGood
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Normalized comparison of the two integral pullback models

Source: Bhatt--Scholze, Lemma 6.5.9(4), Remark 6.8.15; Stacks Tags 0941 and 099N(5).

This comparison concerns ambient derived categories and specified augmentations.
It has no properness, constructibility, completeness, or base-field hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem strictUnit_app {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {U T : Scheme.{u}} (h : U ⟶ T)
    (K : PbcCompletedDerived T d) :
    (pbcActualStrictCompletedPullUnit d h).app K = completedPullbackComparison h d K := by
  simp only [pbcActualStrictCompletedPullUnit, completedPullbackComparison,
    NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp]

/-- Scalar transport identifies ordinary pullback and the entire strict quotient towers.
The induced Roos/derived-limit comparison carries the specified ordinary quotient
augmentation to the specified strict-tower completion unit.

Source: Bhatt--Scholze, Lemma 6.5.9(4), Remark 6.8.15; Stacks Tags 0941 and 099N(5). -/
theorem pbc_proper_integral_strict_model_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T) :
    ∃ (a : PbcProperIntegralPullbackIdentification l E h)
      (b : integralDerivedPullback l E h ⋙ integralDetailedTransport U l E ≅
        integralDetailedTransport T l E ⋙ completedReductionTower T (pbcIntegralDatum l E) ⋙
          completedTowerPullback h (pbcIntegralDatum l E) ⋙
            completedTowerRlim (pbcIntegralDatum l E) U),
      PbcProperIntegralModelMatching l E h a b ∧
      ∀ L : DerivedCategory (integralTowerModules l E T),
        (integralDetailedTransport U l E).map
            ((ordinaryIntegralCompletionComparison l E h).app L) ≫ b.hom.app L =
          a.derivedIso.hom.app L ≫ completedPullbackComparison h (pbcIntegralDatum l E)
            ((integralDetailedTransport T l E).obj L) := by
  obtain ⟨a⟩ := pbc_integral_pullback_identification_exists l E h
  obtain ⟨b, hm⟩ := pbc_integral_strict_model_matching_exists l E h a
  refine ⟨a, b, hm, ?_⟩
  let η := Functor.whiskerRight (ordinaryIntegralCompletionComparison l E h)
    (integralDetailedTransport U l E) ≫ b.hom
  let γ := Functor.whiskerLeft (integralDetailedTransport T l E)
    (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h)
  let δ := a.derivedIso.hom ≫ γ
  have hηδ : η = δ := by
    let ff := Classical.choice (good_whisker_fullyFaithful l E T
      (PbcCompletedDerived U (pbcIntegralDatum l E)))
    apply ff.map_injective
    ext P
    change (integralDetailedTransport U l E).map
          ((ordinaryIntegralCompletionComparison l E h).app (DerivedCategory.Q.obj P.obj)) ≫
          b.hom.app (DerivedCategory.Q.obj P.obj) =
        a.derivedIso.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
            ((integralDetailedTransport T l E).obj (DerivedCategory.Q.obj P.obj))
    rw [strictUnit_app]
    exact pbc_integral_completion_matching_on_good l E h a b hm P
  intro L
  have he := congrArg (fun α ↦ α.app L) hηδ
  change (integralDetailedTransport U l E).map
        ((ordinaryIntegralCompletionComparison l E h).app L) ≫ b.hom.app L =
      a.derivedIso.hom.app L ≫
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
          ((integralDetailedTransport T l E).obj L) at he
  rw [strictUnit_app] at he
  exact he

end WeilConjectures
