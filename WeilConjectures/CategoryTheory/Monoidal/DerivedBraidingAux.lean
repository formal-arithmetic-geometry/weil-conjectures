/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Compatibility of a tensor comparison with braidings, abstractly

For a functor `F : D ⥤ D'` between braided monoidal categories and a natural transformation
`δ : F (K ⊗ M) ⟶ F K ⊗ F M` of bifunctors, the *braided conjugate* of `δ`
(`CategoryTheory.braidedConjugate`) is the natural transformation
`F (K ⊗ M) ⟶ F (M ⊗ K) ⟶ F M ⊗ F K ⟶ F K ⊗ F M` built from `δ` and the braidings. It equals `δ`
exactly when `δ` is compatible with the braidings (`CategoryTheory.δ_braiding_of_eq`).

`CategoryTheory.braidedConjugate_aux` is the computation identifying the braided conjugate of the
tensor comparison of a total left derived functor with the comparison itself on the images of the
localization functor: all the derived functors, counits and comparison maps are variables, and the
inputs are the compatibilities of the localization functors with the braidings and of the
comparison map with the counits.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {D D' : Type*} [Category D] [Category D'] [MonoidalCategory D] [MonoidalCategory D']
  [BraidedCategory D] [BraidedCategory D'] (F : D ⥤ D')

/-- The *braided conjugate* `F (K ⊗ M) ⟶ F (M ⊗ K) ⟶ F M ⊗ F K ⟶ F K ⊗ F M` of a natural
transformation `δ : F (K ⊗ M) ⟶ F K ⊗ F M` of bifunctors. -/
@[simps]
def braidedConjugate
    (δ : curriedTensor D ⋙ (Functor.whiskeringRight D D D').obj F ⟶
      (((Functor.whiskeringLeft₂ D').obj F).obj F).obj (curriedTensor D')) :
    curriedTensor D ⋙ (Functor.whiskeringRight D D D').obj F ⟶
      (((Functor.whiskeringLeft₂ D').obj F).obj F).obj (curriedTensor D') where
  app K :=
    { app M := F.map (β_ K M).hom ≫ (δ.app M).app K ≫ (β_ (F.obj K) (F.obj M)).inv
      naturality M M' g := by
        have h := NatTrans.congr_app (δ.naturality g) K
        dsimp at h ⊢
        rw [← F.map_comp_assoc, BraidedCategory.braiding_naturality_right, F.map_comp,
          Category.assoc, reassoc_of% h, BraidedCategory.braiding_inv_naturality_left]
        simp only [Category.assoc] }
  naturality K K' g := by
    ext M
    have h := (δ.app M).naturality g
    dsimp at h ⊢
    rw [← F.map_comp_assoc, BraidedCategory.braiding_naturality_left, F.map_comp,
      Category.assoc, reassoc_of% h, BraidedCategory.braiding_inv_naturality_right]
    simp only [Category.assoc]

/-- If `δ` equals its braided conjugate, it is compatible with the braidings. -/
lemma δ_braiding_of_eq
    {δ : curriedTensor D ⋙ (Functor.whiskeringRight D D D').obj F ⟶
      (((Functor.whiskeringLeft₂ D').obj F).obj F).obj (curriedTensor D')}
    (h : δ = braidedConjugate F δ) (K M : D) :
    (δ.app K).app M ≫ (β_ (F.obj K) (F.obj M)).hom =
      F.map (β_ K M).hom ≫ (δ.app M).app K := by
  conv_lhs => rw [h]
  simp

variable {X₁ X₂ X₃ X₄ : D} {LP LQ FP FQ W₁ W₂ T₁ T₂ : D'}

omit [MonoidalCategory D] [BraidedCategory D] in
/-- The computation identifying the braided conjugate of a tensor comparison of a derived functor
with the comparison itself on the images of complexes `P`, `Q`; see the module docstring. -/
lemma braidedConjugate_aux (b : X₁ ⟶ X₂) (μPQ : X₁ ⟶ X₃) (μQP : X₂ ⟶ X₄) (qβ : X₃ ⟶ X₄)
    (δQP : F.obj X₂ ⟶ LQ ⊗ LP) (εP : LP ⟶ FP) (εQ : LQ ⟶ FQ) (m₁ : FP ⊗ FQ ⟶ W₁)
    (m₂ : FQ ⊗ FP ⟶ W₂) (c₁ : W₂ ⟶ W₁) (tPQ : W₁ ⟶ T₁) (tQP : W₂ ⟶ T₂) (c₂ : T₂ ⟶ T₁)
    (εPQ : F.obj X₃ ⟶ T₁) (εQP : F.obj X₄ ⟶ T₂) (c₃ : T₁ ⟶ T₂)
    (hb : (β_ FP FQ).inv ≫ m₁ = m₂ ≫ c₁) (hc : c₁ ≫ tPQ = tQP ≫ c₂)
    (hd : δQP ≫ (εQ ⊗ₘ εP) ≫ m₂ ≫ tQP = F.map μQP ≫ εQP) (he : b ≫ μQP = μPQ ≫ qβ)
    (hf : F.map qβ ≫ εQP = εPQ ≫ c₃) (hg : c₃ ≫ c₂ = 𝟙 _) :
    F.map b ≫ δQP ≫ (β_ LP LQ).inv ≫ (εP ⊗ₘ εQ) ≫ m₁ ≫ tPQ = F.map μPQ ≫ εPQ := by
  rw [← BraidedCategory.braiding_inv_naturality_assoc, reassoc_of% hb, hc,
    reassoc_of% hd, ← F.map_comp_assoc, he, F.map_comp, Category.assoc, reassoc_of% hf, hg,
    Category.comp_id]

end CategoryTheory
