/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeConstantSupportModel
import all WeilConjectures.AlgebraicGeometry.IntegralQuotientResolutionNormalization

/-! # K-injective preservation for constant scalar restriction

Restriction from completed to constant coefficients is right adjoint to exact
scalar extension along the flat constant-to-completed coefficient map.
(blueprint: lem-pur-compact-support-scalar-limit-restriction-kinjective).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.IntegralQuotient
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The strict tower restriction to constant scalars preserves K-injectives.
Source: Stacks 093M (flat completion) and 08BJ (the exact-adjunction criterion).
(blueprint: lem-pur-compact-support-scalar-limit-restriction-kinjective).
Proof: identify the actual quotient tower with the powers of the lifted
uniformizer ideal, using the existing quotient and completion comparisons.
The limit-lift equations identify the given constant-to-completed map with
the canonical completion map. The integral coefficient ring is Noetherian,
so flat completion makes its scalar extension exact. Whisker the scalar
adjunction over the tower index. Its left adjoint remains exact pointwise;
the exact-adjunction criterion therefore proves preservation of K-injectives. -/
theorem scalarRestriction_preservesKInjective (W : Scheme.{u}) :
    (towerConstantRestriction l E W).PreservesKInjectiveComplexes := by
  let F := adicLisseForget W
  let S := completedIntegralCommRingSheafUnrestricted l E W
  let e : adicLisseCompletedRing W (liftedIdeal l E) ≅ S :=
    F.preimageIso (completionRingIso l E W)
  let c : adicLisseConstantRing W
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶ S :=
    F.preimage (integralConstantToCompletionOfUniverses l E W)
  have hc : ∀ n : ℕ,
      c ≫ e.inv ≫ limit.π (adicLisseRingSystem W (liftedIdeal l E)) (op n) =
        (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk ((liftedIdeal l E) ^ (n + 1)))) := by
    intro n
    apply F.map_injective
    simp only [Functor.map_comp, c, Functor.map_preimage, e, Functor.preimageIso_inv]
    apply (cancel_mono (finiteCompletionIso l E W n).hom).mp
    rw [completion_scalar]
    simp only [Category.assoc]
    rw [← completionRingIso_projection]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact limit.lift_π (integralConstantConeOfUniverses l E W) (op n)
  let : IsNoetherianRing (Padic.coefficientExtensionIntegers l E) := coefficient_noetherian l E
  let : IsNoetherianRing (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
    isNoetherianRing_of_ringEquiv _ ULift.ringEquiv.symm
  have h := (completed_constant_algebra_flat_quotients W (liftedIdeal l E) S e c hc).2.1
  have hlim : PreservesFiniteLimits (pbcExtend c) := (exactFunctor_iff _).1 h |>.1
  have hcolim : PreservesFiniteColimits (pbcExtend c) := (exactFunctor_iff _).1 h |>.2
  have htlim : PreservesFiniteLimits
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend c)) := ⟨fun _ _ _ ↦ inferInstance⟩
  have htcolim : PreservesFiniteColimits
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend c)) := ⟨fun _ _ _ ↦ inferInstance⟩
  have hki := ((pbcScalarAdjunction c).whiskerRight ℕᵒᵖ).preservesKInjectiveComplexes
  simp only [pbcRestrict, proEtaleRingRestrictScalars, c, F, Functor.map_preimage] at hki
  convert hki using 1 <;> rfl

end WeilConjectures.PurStrictScalar
