/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates with respect to derived adjunctions

Let `adj₁ : G₁ ⊣ F₁` and `adj₂ : G₂ ⊣ F₂` be adjunctions, `σ : H₁ ⋙ G₂ ⟶ G₁ ⋙ H₂` a square of
functors and `θ : H₁' ⋙ G₂' ⟶ G₁' ⋙ H₂'` a square of functors between localized categories
which is computed by `σ` (modulo given natural transformations `γᵢ : Lᵢ ⋙ Hᵢ' ⟶ Hᵢ ⋙ L'ᵢ`
comparing `Hᵢ'` with `Hᵢ`). Then the mate of `θ` with respect to the derived adjunctions
`Adjunction.derived` is computed by the mate of `σ`, through the units `β` of the derived right
adjoints (`CategoryTheory.Adjunction.derived_mateEquiv_app_fac`).
-/

@[expose] public section

open CategoryTheory.Functor

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄]
  {G₁ : C₁ ⥤ C₂} {F₁ : C₂ ⥤ C₁} (adj₁ : G₁ ⊣ F₁) {G₂ : C₃ ⥤ C₄} {F₂ : C₄ ⥤ C₃} (adj₂ : G₂ ⊣ F₂)
  {H₁ : C₁ ⥤ C₃} {H₂ : C₂ ⥤ C₄}
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} {L₄ : C₄ ⥤ D₄}
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  (W₄ : MorphismProperty C₄)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃] [L₄.IsLocalization W₄]
  {G₁' : D₁ ⥤ D₂} {F₁' : D₂ ⥤ D₁} {G₂' : D₃ ⥤ D₄} {F₂' : D₄ ⥤ D₃}
  {H₁' : D₁ ⥤ D₃} {H₂' : D₂ ⥤ D₄}
  (α₁ : L₁ ⋙ G₁' ⟶ G₁ ⋙ L₂) (β₁ : F₁ ⋙ L₁ ⟶ L₂ ⋙ F₁')
  (α₂ : L₃ ⋙ G₂' ⟶ G₂ ⋙ L₄) (β₂ : F₂ ⋙ L₃ ⟶ L₄ ⋙ F₂')
  (γ₁ : L₁ ⋙ H₁' ⟶ H₁ ⋙ L₃) (γ₂ : L₂ ⋙ H₂' ⟶ H₂ ⋙ L₄)
  [G₁'.IsLeftDerivedFunctor α₁ W₁] [F₁'.IsRightDerivedFunctor β₁ W₂]
  [(G₁' ⋙ F₁').IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫ whiskerRight α₁ F₁') W₁]
  [(F₁' ⋙ G₁').IsRightDerivedFunctor (whiskerRight β₁ G₁' ≫ (Functor.associator _ _ _).hom) W₂]
  [G₂'.IsLeftDerivedFunctor α₂ W₃] [F₂'.IsRightDerivedFunctor β₂ W₄]
  [(G₂' ⋙ F₂').IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫ whiskerRight α₂ F₂') W₃]
  [(F₂' ⋙ G₂').IsRightDerivedFunctor (whiskerRight β₂ G₂' ≫ (Functor.associator _ _ _).hom) W₄]

namespace Adjunction

/-- **The derived mate is computed by the underived mate.** Let `θ : H₁' ⋙ G₂' ⟶ G₁' ⋙ H₂'` be a
square between the derived functors which, on the object `L₁ (F₁ K)`, is computed by a square
`σ : H₁ ⋙ G₂ ⟶ G₁ ⋙ H₂` of underived functors through the comparison maps `αᵢ` of the derived
left adjoints and `γᵢ` of the functors `Hᵢ'` (hypothesis `hθ`). Then the mate of `θ` with respect
to the derived adjunctions `adj₁.derived` and `adj₂.derived`, at `L₂ K` and read through the
comparison maps `β₁` and `γ₂`, is the mate of `σ` followed by the comparison map `β₂`. -/
theorem derived_mateEquiv_app_fac (σ : TwoSquare H₁ G₁ G₂ H₂) (θ : TwoSquare H₁' G₁' G₂' H₂')
    (K : C₂)
    (hθ : θ.natTrans.app (L₁.obj (F₁.obj K)) ≫ H₂'.map (α₁.app (F₁.obj K)) ≫
        γ₂.app (G₁.obj (F₁.obj K)) =
      G₂'.map (γ₁.app (F₁.obj K)) ≫ α₂.app (H₁.obj (F₁.obj K)) ≫
        L₄.map (σ.natTrans.app (F₁.obj K))) :
    H₁'.map (β₁.app K) ≫ (mateEquiv (adj₁.derived W₁ W₂ α₁ β₁) (adj₂.derived W₃ W₄ α₂ β₂)
        θ).natTrans.app (L₂.obj K) ≫ F₂'.map (γ₂.app K) =
      γ₁.app (F₁.obj K) ≫ L₃.map ((mateEquiv adj₁ adj₂ σ).natTrans.app K) ≫
        β₂.app (H₂.obj K) := by
  have hmate (Z : D₂) : (mateEquiv (adj₁.derived W₁ W₂ α₁ β₁) (adj₂.derived W₃ W₄ α₂ β₂)
      θ).natTrans.app Z = (adj₂.derived W₃ W₄ α₂ β₂).unit.app (H₁'.obj (F₁'.obj Z)) ≫
        F₂'.map (θ.natTrans.app (F₁'.obj Z)) ≫
        F₂'.map (H₂'.map ((adj₁.derived W₁ W₂ α₁ β₁).counit.app Z)) := by
    simp [mateEquiv_apply]
  have hmate' : (mateEquiv adj₁ adj₂ σ).natTrans.app K =
      adj₂.unit.app (H₁.obj (F₁.obj K)) ≫ F₂.map (σ.natTrans.app (F₁.obj K)) ≫
        F₂.map (H₂.map (adj₁.counit.app K)) := by
    simp [mateEquiv_apply]
  have h₁ := (adj₂.derived W₃ W₄ α₂ β₂).unit.naturality (H₁'.map (β₁.app K))
  have h₂ := θ.natTrans.naturality (β₁.app K)
  have h₃ := adj₁.derivedε_fac_app W₂ α₁ β₁ K
  have h₄ := γ₂.naturality (adj₁.counit.app K)
  have h₅ := (adj₂.derived W₃ W₄ α₂ β₂).unit.naturality (γ₁.app (F₁.obj K))
  have h₆ := adj₂.derivedη_fac_app W₃ α₂ β₂ (H₁.obj (F₁.obj K))
  have h₇ := β₂.naturality (σ.natTrans.app (F₁.obj K) ≫ H₂.map (adj₁.counit.app K))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂ h₄ h₅ h₇
  simp only [derived_unit, derived_counit] at hmate h₁ h₅ ⊢
  rw [hmate]
  simp only [Category.assoc]
  rw [reassoc_of% h₁]
  simp only [← Functor.map_comp]
  rw [reassoc_of% h₂, ← Functor.map_comp_assoc H₂', h₃, Functor.map_comp_assoc, h₄,
    reassoc_of% hθ]
  simp only [Functor.map_comp]
  rw [← reassoc_of% h₅, reassoc_of% h₆, hmate']
  simp only [Functor.map_comp, Category.assoc] at h₇ ⊢
  rw [← h₇]

end Adjunction

end CategoryTheory
