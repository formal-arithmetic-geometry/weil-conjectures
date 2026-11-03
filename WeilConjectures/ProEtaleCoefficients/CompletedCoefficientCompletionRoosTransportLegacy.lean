/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.ActualCompletedReductionReconstructionLegacy
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedQuotientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.CompletedKoszulReductionRoosTriangleLegacy
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import all WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The normalized completion Roos triangle under coefficient transport

Legacy copy (interface repository, batch a5/27): the earlier proved statement over the
actual completed coefficient presentation, kept for its importers after X3 restated
`Sheaf.Paper.CompletedCoefficientCompletionRoosTransport` over the pulled-back condensed
coefficients.

Source: Stacks Tags 099M, 099N and 06YY; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-pur-completed-coefficient-completion-roos-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

open Opposite
open IntegralCoefficientPresentation
attribute [local instance 30000] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
attribute [local irreducible] completedReductionEvaluation
  scalarReductionExistence scalarReductionDerivedExistence scalarReductionDerivedExtension
  scalarReductionExtension scalarReductionCounit normalizedDVRResCompletedComp
  completedIntegralCoefficientSheafUnrestricted normalizedDVRKFlatComparison
  CategoryTheory.Limits.limit

attribute [local irreducible] Functor.mapDerivedCategory

attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

attribute [local irreducible] tensorRestrictionComp moduleRestrictionComp
  pbcDerivedScalarAdjunction reductionDerivedChange
  normalizedDVRQuotient integralCoefficientSheafTransition

/-- Transport of the completion reflector, retaining its unit and the canonical
intrinsic reduction maps. This compares completion objects before imposing any
completeness, boundedness or constructibility condition on the input.

Source: Stacks Tags 099M, 099N and 06YY; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-pur-completed-coefficient-completion-roos-transport).

Proof: the equation on the coefficient isomorphism identifies its finite projections
with the already normalized integralDetailedLevelComparison. At each positive level,
the tensor/restriction adjunction therefore identifies reduction after inverse scalar
restriction with sfDerivedReductionRestricted. On flat K-flat representatives these
maps send a pure tensor to the same tensor with its coefficient transported. The
transition squares and augmentation squares follow on these tensors and descend by
the universal derived tensor counits. Thus this is an isomorphism of the augmented
reduction sequences, including their canonical units, rather than only levelwise
isomorphisms of their objects.

Apply completedKoszulQuotientComparison and completedKoszulReductionRoosTriangle to
an intrinsic completed-coefficient representative. The Koszul reflector and the
actual complete-subcategory reflector represent the same adjunction, so their unique
unit-compatible comparison identifies the first vertex with pbcActualCompletion K.
Exact restriction along the inverse ring isomorphism preserves products and
triangles. Transport the resulting Roos triangle through the preceding sequence
isomorphism. Its coordinate unit equations give the displayed product unit equation
by product extensionality. All comparisons use the positive quotient levels; the
argument also applies to the zero object, the empty scheme and residue level one. -/
theorem completedCoefficientCompletionRoosTransport_legacy
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (c : pbcAdicCompletion W (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E W)
    (_hc : (adicLisseForget W).mapIso c = integralDetailedCoefficientComparison W l E)
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    ∃ hp : HasProduct (fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj
        ((pbcDerivedRestrict c.inv).obj K)),
      letI := hp
      ∃ (p : (pbcDerivedRestrict c.inv).obj
          ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) ⟶
          ∏ᶜ fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj
            ((pbcDerivedRestrict c.inv).obj K))
        (δ : (∏ᶜ fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj
            ((pbcDerivedRestrict c.inv).obj K)) ⟶
          ((pbcDerivedRestrict c.inv).obj
            ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K))⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle
          (fun n ↦ (sfDerivedReductionTransition l E W n).app
            ((pbcDerivedRestrict c.inv).obj K))
          ((pbcDerivedRestrict c.inv).obj
            ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K)) p δ ∧
        (pbcDerivedRestrict c.inv).map
            ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K) ≫ p =
          Pi.lift (fun n ↦ (sfDerivedReductionUnit l E W n).app
            ((pbcDerivedRestrict c.inv).obj K)) := by
  classical
  let F := (pbcRestrict c.hom).mapDerivedCategory
  let H := (pbcRestrict c.inv).mapDerivedCategory
  let hF₀ : (pbcRestrict c.hom).IsEquivalence := (restrict_equivalence c).1
  let hH₀ : (pbcRestrict c.inv).IsEquivalence := (restrict_equivalence c).2.1
  let : F.IsEquivalence := by
    change (pbcRestrict c.hom).mapDerivedCategory.IsEquivalence
    infer_instance
  let : H.IsEquivalence := by
    change (pbcRestrict c.inv).mapDerivedCategory.IsEquivalence
    infer_instance
  let : F.CommShift ℤ := by dsimp only [F]; infer_instance
  let : F.IsTriangulated := by dsimp only [F]; infer_instance
  let : F.Additive := by dsimp only [F]; infer_instance
  let round : H ⋙ F ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso (pbcRestrict c.inv) (pbcRestrict c.hom)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (pbcRestrictComp c.hom c.inv (𝟙 _) c.hom_inv_id ≪≫ restrictId _) ≪≫
      Functor.mapDerivedCategoryIdIso _
  let := derived_products W (completedIntegralCommRingSheafUnrestricted l E W)
  let := derived_products W (pbcAdicCompletion W (pbcIntegralDatum l E))
  obtain ⟨β, hβu, hβt⟩ := coefficientReductionComparison l E W c _hc
  dsimp only [pbcDerivedRestrict] at β hβu hβt
  let J := H.obj K
  let R n := IntegralCoefficientPresentation.reduction
    (pbcAdicProjection W (pbcIntegralDatum l E) n)
  let a (n : ℕ) : F.obj ((sfDerivedReductionRestricted l E W n).obj J) ≅ (R n).obj K :=
    (β J n).symm ≪≫ (R n).mapIso (round.app K)
  have ha (n : ℕ) :
      F.map ((sfDerivedReductionTransition l E W n).app J) ≫ (a n).hom =
        (a (n + 1)).hom ≫ (reconstructionStep W (pbcIntegralDatum l E) n).app K := by
    apply (cancel_epi (β J (n + 1)).hom).1
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hβt]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact ((reconstructionStep W (pbcIntegralDatum l E) n).naturality (round.hom.app K)).symm
  obtain ⟨hp, p, δ, hδ, hu⟩ := pbcNormalizedRoos W (pbcIntegralDatum l E) K
  let := hp
  refine ⟨inferInstance, ?_⟩
  have huv (n : ℕ) :
      F.map (H.map ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K)) ≫
        (round.app ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K)).hom ≫
        p ≫ Pi.π _ n =
      F.map ((sfDerivedReductionUnit l E W n).app J) ≫ (a n).hom := by
    change (H ⋙ F).map _ ≫ round.hom.app _ ≫ p ≫ Pi.π _ n = _
    rw [round.hom.naturality_assoc]
    dsimp only [Functor.id_map, Functor.id_obj]
    erw [hu]
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← hβu]
    have hh := congrArg (fun f ↦
      (pbcDerivedScalarAdjunction (pbcAdicProjection W (pbcIntegralDatum l E) n)).unit.app
        (F.obj J) ≫ f) ((β J n).hom_inv_id_assoc ((R n).map (round.app K).hom))
    have hh' := (Category.assoc _ _ _).trans hh
    refine Eq.trans ?_ hh'.symm
    have hn := (pbcDerivedScalarAdjunction
      (pbcAdicProjection W (pbcIntegralDatum l E) n)).unit.naturality
        (round.hom.app K)
    simpa only [Functor.id_map, Functor.id_obj, Iso.app_hom, J, R,
      IntegralCoefficientPresentation.reduction, Functor.comp_obj, Functor.comp_map] using hn
  obtain ⟨p', δ', hδ', hu'⟩ := reflectNormalizedRoos F a
    (fun n ↦ (sfDerivedReductionTransition l E W n).app J)
    (fun n ↦ (reconstructionStep W (pbcIntegralDatum l E) n).app K) ha
    (round.app ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K)) p δ hδ
    (H.map ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K))
    (fun n ↦ (sfDerivedReductionUnit l E W n).app J) huv
  refine ⟨p', δ', hδ', ?_⟩
  apply Pi.hom_ext
  intro n
  simpa only [Category.assoc, Pi.lift_π, H, J, pbcDerivedRestrict] using hu' n

end WeilConjectures
