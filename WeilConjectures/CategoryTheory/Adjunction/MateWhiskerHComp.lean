/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates of whiskered and composed squares

The mates correspondence `mateEquiv` turns the whiskering of a square at the top
into the whiskering of the mate on the right. Combined with `mateEquiv_vcomp`, a
compatibility `α₃ ∘ τ_G = τ_H ∘ (α₁ ≫ₕ α₂)` between squares along three adjunctions is equivalent
to the corresponding compatibility between their mates.
-/

@[expose] public section

namespace CategoryTheory

open TwoSquare

section

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mate of a square whiskered at the top is the mate whiskered on the right. -/
lemma mateEquiv_whiskerTop {G' : A ⥤ C} (α : TwoSquare G L₁ L₂ H) (σ : G' ⟶ G) :
    mateEquiv adj₁ adj₂ (α.whiskerTop σ) = (mateEquiv adj₁ adj₂ α).whiskerRight σ := by
  ext X
  simp

end

variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* E] [Category* F] {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₃ : E ⥤ F} {R₃ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
  {G₁ : A ⥤ C} {H₁ : B ⥤ D} {G₂ : C ⥤ E} {H₂ : D ⥤ F} {G₃ : A ⥤ E} {H₃ : B ⥤ F}

/-- A square `α₃` along `G₃` is compatible with the horizontal composite of squares `α₁`, `α₂`
along `τ_G : G₁ ⋙ G₂ ⟶ G₃` and `τ_H : H₁ ⋙ H₂ ⟶ H₃` if and only if the mates are compatible. -/
lemma whiskerTop_eq_hComp_whiskerBottom_iff (α₁ : TwoSquare G₁ L₁ L₂ H₁)
    (α₂ : TwoSquare G₂ L₂ L₃ H₂) (α₃ : TwoSquare G₃ L₁ L₃ H₃) (τG : G₁ ⋙ G₂ ⟶ G₃)
    (τH : H₁ ⋙ H₂ ⟶ H₃) :
    α₃.whiskerTop τG = (α₁ ≫ₕ α₂).whiskerBottom τH ↔
      (mateEquiv adj₁ adj₃ α₃).whiskerRight τG =
        (mateEquiv adj₁ adj₂ α₁ ≫ᵥ mateEquiv adj₂ adj₃ α₂).whiskerLeft τH := by
  rw [← mateEquiv_whiskerTop, ← mateEquiv_vcomp, ← mateEquiv_whiskerBottom,
    (mateEquiv adj₁ adj₃).apply_eq_iff_eq]

/-- Componentwise form of `whiskerTop_eq_hComp_whiskerBottom_iff`: the mates of compatible squares
are compatible. -/
lemma app_comp_mateEquiv_app_of_whiskerRight_comp_eq (α₁ : TwoSquare G₁ L₁ L₂ H₁)
    (α₂ : TwoSquare G₂ L₂ L₃ H₂) (α₃ : TwoSquare G₃ L₁ L₃ H₃) (τG : G₁ ⋙ G₂ ⟶ G₃)
    (τH : H₁ ⋙ H₂ ⟶ H₃)
    (h : Functor.whiskerRight τG L₃ ≫ α₃ =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft G₁ α₂ ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α₁ H₂ ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft L₁ τH) (X : B) :
    τG.app (R₁.obj X) ≫ (mateEquiv adj₁ adj₃ α₃).app X =
      G₂.map ((mateEquiv adj₁ adj₂ α₁).app X) ≫ (mateEquiv adj₂ adj₃ α₂).app (H₁.obj X) ≫
        R₃.map (τH.app X) := by
  have h' : α₃.whiskerTop τG = (α₁ ≫ₕ α₂).whiskerBottom τH := by
    ext Y
    simpa using NatTrans.congr_app h Y
  simpa using NatTrans.congr_app
    ((whiskerTop_eq_hComp_whiskerBottom_iff adj₁ adj₂ adj₃ α₁ α₂ α₃ τG τH).1 h') X

/-- Let `e₁`, `e₂`, `e₃` be invertible squares, whose inverses have mates compatible with
`τ_G : G₁ ⋙ G₂ ⟶ G₃` and `τ_H : H₁ ⋙ H₂ ⟶ H₃`. Then `e₁`, `e₂`, `e₃` are compatible with
`τ_G` and `τ_H`. -/
lemma app_comp_hom_app_of_mateEquiv_inv (e₁ : L₁ ⋙ H₁ ≅ G₁ ⋙ L₂) (e₂ : L₂ ⋙ H₂ ≅ G₂ ⋙ L₃)
    (e₃ : L₁ ⋙ H₃ ≅ G₃ ⋙ L₃) (τG : G₁ ⋙ G₂ ⟶ G₃) (τH : H₁ ⋙ H₂ ⟶ H₃)
    (h : Functor.whiskerLeft R₁ τG ≫ mateEquiv adj₁ adj₃ e₃.inv =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (mateEquiv adj₁ adj₂ e₁.inv) G₂ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft H₁ (mateEquiv adj₂ adj₃ e₂.inv) ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight τH R₃) (X : A) :
    τH.app (L₁.obj X) ≫ e₃.hom.app X =
      H₂.map (e₁.hom.app X) ≫ e₂.hom.app (G₁.obj X) ≫ L₃.map (τG.app X) := by
  have h' : (mateEquiv adj₁ adj₃ e₃.inv).whiskerRight τG =
      (mateEquiv adj₁ adj₂ e₁.inv ≫ᵥ mateEquiv adj₂ adj₃ e₂.inv).whiskerLeft τH := by
    ext Y
    simpa using NatTrans.congr_app h Y
  have hX := NatTrans.congr_app
    ((whiskerTop_eq_hComp_whiskerBottom_iff adj₁ adj₂ adj₃ e₁.inv e₂.inv e₃.inv τG τH).2 h') X
  simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app, TwoSquare.hComp_app,
    Category.assoc] at hX
  rw [← cancel_mono (e₃.inv.app X), ← cancel_epi (H₂.map (e₁.inv.app X)),
    ← cancel_epi (e₂.inv.app (G₁.obj X))]
  simpa using hX.symm

/-- If invertible squares `α₁`, `α₂`, `α₃` are compatible with `τ_G : G₁ ⋙ G₂ ⟶ G₃` and
`τ_H : H₁ ⋙ H₂ ⟶ H₃`, so are their inverses. -/
lemma whiskerLeft_comp_inv_eq_of_whiskerRight_comp_hom_eq (α₁ : G₁ ⋙ L₂ ≅ L₁ ⋙ H₁)
    (α₂ : G₂ ⋙ L₃ ≅ L₂ ⋙ H₂) (α₃ : G₃ ⋙ L₃ ≅ L₁ ⋙ H₃) (τG : G₁ ⋙ G₂ ⟶ G₃)
    (τH : H₁ ⋙ H₂ ⟶ H₃)
    (h : Functor.whiskerRight τG L₃ ≫ α₃.hom =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft G₁ α₂.hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α₁.hom H₂ ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft L₁ τH) :
    Functor.whiskerLeft L₁ τH ≫ α₃.inv =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α₁.inv H₂ ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft G₁ α₂.inv ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight τG L₃ := by
  ext X
  have hX := NatTrans.congr_app h X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at hX
  rw [← cancel_mono (α₃.hom.app X)]
  simp only [Category.assoc, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id, hX]
  simp [← Functor.map_comp_assoc]

end CategoryTheory
