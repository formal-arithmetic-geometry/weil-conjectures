/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.DerivedForgetMateNormalization
public import WeilConjectures.CategoryTheory.Adjunction.MatesHCompIsIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # Normalization of the derived mate of a composite realization -/

@[expose] public noncomputable section

open CategoryTheory Limits Abelian

namespace CategoryTheory

section Mates

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category* C₀] [Category* C₁] [Category* C₂]
  [Category* D₀] [Category* D₁] [Category* D₂]
  {L₀ : D₀ ⥤ C₀} {R₀ : C₀ ⥤ D₀} {L₁ : D₁ ⥤ C₁} {R₁ : C₁ ⥤ D₁}
  {L₂ : D₂ ⥤ C₂} {R₂ : C₂ ⥤ D₂}
  (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
  {U₁ : D₀ ⥤ D₁} {V₁ : C₀ ⥤ C₁} {U₂ : D₁ ⥤ D₂} {V₂ : C₁ ⥤ C₂}

/-- The inverse horizontal composite of two right-adjoint squares is the mate of the
horizontal composite of their left-adjoint squares. -/
lemma mateEquiv_isoHComp_eq
    (α₁ : U₁ ⋙ L₁ ≅ L₀ ⋙ V₁) (α₂ : U₂ ⋙ L₂ ≅ L₁ ⋙ V₂)
    (β₁ : R₀ ⋙ U₁ ≅ V₁ ⋙ R₁) (β₂ : R₁ ⋙ U₂ ≅ V₂ ⋙ R₂)
    (h₁ : (mateEquiv a₀ a₁ α₁.hom).natTrans = β₁.hom)
    (h₂ : (mateEquiv a₁ a₂ α₂.hom).natTrans = β₂.hom) :
    (mateEquiv a₀ a₂ (Functor.isoHComp α₁ α₂).hom).natTrans =
      (Functor.isoHComp β₁.symm β₂.symm).inv := by
  rw [Functor.isoHComp_hom, mateEquiv_vcomp a₀ a₁ a₂]
  ext M
  simp [TwoSquare.vComp, h₁, h₂, Functor.isoHComp]

end Mates

namespace Functor

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category* C₀] [Category* C₁] [Category* C₂]
  [Category* D₀] [Category* D₁] [Category* D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  [HasKInjectiveResolutions C₀] [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₂]
  {R₀ : C₀ ⥤ D₀} {R₁ : C₁ ⥤ D₁} {R₂ : C₂ ⥤ D₂}
  [R₀.Additive] [R₁.Additive] [R₂.Additive]
  {U₁ : D₀ ⥤ D₁} {V₁ : C₀ ⥤ C₁} {U₂ : D₁ ⥤ D₂} {V₂ : C₁ ⥤ C₂}
  [U₁.Additive] [V₁.Additive] [U₂.Additive] [V₂.Additive]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits V₁] [PreservesFiniteColimits V₁]
  [PreservesFiniteLimits V₂] [PreservesFiniteColimits V₂]
  [V₁.PreservesKInjectiveComplexes] [V₂.PreservesKInjectiveComplexes]

/-- A derived commutation square for a composite realization factors through the two
derived commutation squares, with the exact-functor composition isomorphisms. -/
lemma rightDerivedFunctorCommIso_isoHComp_inv_app
    (β₁ : R₀ ⋙ U₁ ≅ V₁ ⋙ R₁) (β₂ : R₁ ⋙ U₂ ≅ V₂ ⋙ R₂)
    (M : DerivedCategory C₀) :
    (rightDerivedFunctorCommIso (Functor.isoHComp β₁.symm β₂.symm).symm).hom.app M =
      (mapDerivedCategoryCompIso U₁ U₂).hom.app (R₀.rightDerivedFunctor.obj M) ≫
        U₂.mapDerivedCategory.map ((rightDerivedFunctorCommIso β₁).hom.app M) ≫
        (rightDerivedFunctorCommIso β₂).hom.app (V₁.mapDerivedCategory.obj M) ≫
        R₂.rightDerivedFunctor.map ((mapDerivedCategoryCompIso V₁ V₂).inv.app M) := by
  have h := rightDerivedFunctorCommIso_hom_app_comp β₂ β₁
    (Functor.isoHComp β₁.symm β₂.symm).symm (Iso.refl _) (Iso.refl _)
    (fun K ↦ by simp [Functor.isoHComp]) M
  simpa only [mapDerivedCategoryNatIso_refl, Iso.trans_refl, Iso.symm_inv, Iso.symm_hom]
    using h

end Functor

end CategoryTheory
