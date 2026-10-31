/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingIntrinsicRestrictionCompLhs

/-! Natural-transformation form of intrinsic finite-dualizing restriction composition. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
private def restrictionCompRhs
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {R₀₁ : C₀ ⥤ C₁} {R₁₂ : C₁ ⥤ C₂} {R₀₂ : C₀ ⥤ C₂}
    {F₀ : C₀ ⥤ D₀} {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂}
    {U₀₁ : D₀ ⥤ D₁} {U₁₂ : D₁ ⥤ D₂}
    (c : R₀₂ ⟶ R₀₁ ⋙ R₁₂) (a : R₁₂ ⋙ F₂ ⟶ F₁ ⋙ U₁₂)
    (b : R₀₁ ⋙ F₁ ⟶ F₀ ⋙ U₀₁) : R₀₂ ⋙ F₂ ⟶ F₀ ⋙ U₀₁ ⋙ U₁₂ :=
  Functor.whiskerRight c F₂ ≫ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft R₀₁ a ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight b U₁₂ ≫ (Functor.associator _ _ _).hom

private theorem restrictionCompRhs_app
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {R₀₁ : C₀ ⥤ C₁} {R₁₂ : C₁ ⥤ C₂} {R₀₂ : C₀ ⥤ C₂}
    {F₀ : C₀ ⥤ D₀} {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂}
    {U₀₁ : D₀ ⥤ D₁} {U₁₂ : D₁ ⥤ D₂}
    (c : R₀₂ ⟶ R₀₁ ⋙ R₁₂) (a : R₁₂ ⋙ F₂ ⟶ F₁ ⋙ U₁₂)
    (b : R₀₁ ⋙ F₁ ⟶ F₀ ⋙ U₀₁) (K : C₀) :
    (restrictionCompRhs c a b).app K =
      F₂.map (c.app K) ≫ a.app (R₀₁.obj K) ≫ U₁₂.map (b.app K) := by
  simp only [restrictionCompRhs, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (X : Scheme.{u})

/-- The Qh comparison extends by localization to a natural-transformation identity.
Source: the localization extension step in the intrinsic restriction composition proof
(blueprint: lem-coef-dualizing-intrinsic-restriction-comp-nattrans-x7).

The Qh case is the section-level pasting calculation. Exact localization and
naturality extend it to all derived objects. -/
theorem finiteDualizingIntrinsicRestriction_comp_natTrans_exists
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    ∃ rhs :
        (Sheaf.derivedRestrictScalars (ProEt.topology X)
            (finiteDualizingQuotient l E (hmn.trans hrm)) ⋙
          (sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (r + 1))).functor) ⟶
        (sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
          normalizedDVRRes l E X hmn ⋙ normalizedDVRRes l E X hrm,
      finiteDualizingIntrinsicRestrictionCompLhs l E X hrm hmn = rhs ∧
      ∀ K, rhs.app K =
        (sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (r + 1))).functor.map
          ((Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X)
            (finiteDualizingQuotient_comp l E hrm hmn)).inv.app K) ≫
          (finiteDualizingIntrinsicRestriction l E X hrm).inv.app
            ((Sheaf.derivedRestrictScalars (ProEt.topology X)
              (finiteDualizingQuotient l E hmn)).obj K) ≫
          (normalizedDVRRes l E X hrm).map
            ((finiteDualizingIntrinsicRestriction l E X hmn).inv.app K) := by
  let rhs := restrictionCompRhs
    (Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X)
      (finiteDualizingQuotient_comp l E hrm hmn)).inv
    (finiteDualizingIntrinsicRestriction l E X hrm).inv
    (finiteDualizingIntrinsicRestriction l E X hmn).inv
  refine ⟨rhs, ?_, fun K ↦ restrictionCompRhs_app _ _ _ K⟩
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro P
  rw [restrictionCompRhs_app]
  exact finiteDualizingIntrinsicRestriction_comp_Qh l E X hrm hmn P
end WeilConjectures
