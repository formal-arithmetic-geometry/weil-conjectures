/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateVCompIsIso

/-! # Components of a vertically composed and whiskered 2-square

The component formula for the square `((α ≫ᵥ β).whiskerLeft e.inv).whiskerRight e'.hom` of
`CategoryTheory.isIso_mateEquiv_vComp_whiskerLeft_whiskerRight`, so that a concrete composite
comparison can be identified with it by an equation of components, without `convert`. -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

open TwoSquare

variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* E] [Category* F]

/-- The components of the stacked square. -/
lemma TwoSquare.vComp_whiskerLeft_whiskerRight_natTrans_app {G : A ⥤ D} {H : B ⥤ E}
    {K : C ⥤ F} {L₁ : A ⥤ B} {L₂ : D ⥤ E} {L₃ : B ⥤ C} {L₄ : E ⥤ F} {L : A ⥤ C} {L' : D ⥤ F}
    (e : L ≅ L₁ ⋙ L₃) (e' : L' ≅ L₂ ⋙ L₄) (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K)
    (M : A) :
    (((α ≫ᵥ β).whiskerLeft e.inv).whiskerRight e'.hom).natTrans.app M =
      e'.hom.app (G.obj M) ≫ L₄.map (α.natTrans.app M) ≫ β.natTrans.app (L₁.obj M) ≫
        K.map (e.inv.app M) := by
  simp [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight]

/-- A composite square given by the components of the stacked square equals it. -/
lemma TwoSquare.vComp_whiskerLeft_whiskerRight_eq {G : A ⥤ D} {H : B ⥤ E}
    {K : C ⥤ F} {L₁ : A ⥤ B} {L₂ : D ⥤ E} {L₃ : B ⥤ C} {L₄ : E ⥤ F} {L : A ⥤ C} {L' : D ⥤ F}
    (e : L ≅ L₁ ⋙ L₃) (e' : L' ≅ L₂ ⋙ L₄) (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K)
    (γ : TwoSquare G L L' K)
    (hγ : ∀ M, γ.natTrans.app M = e'.hom.app (G.obj M) ≫ L₄.map (α.natTrans.app M) ≫
      β.natTrans.app (L₁.obj M) ≫ K.map (e.inv.app M)) :
    ((α ≫ᵥ β).whiskerLeft e.inv).whiskerRight e'.hom = γ :=
  TwoSquare.ext _ _ fun M ↦ by
    rw [TwoSquare.vComp_whiskerLeft_whiskerRight_natTrans_app, hγ]

end CategoryTheory
