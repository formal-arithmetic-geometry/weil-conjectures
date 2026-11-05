/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Composing reduction and site-reading squares -/

@[expose] public section

namespace CategoryTheory

/-- A reduction square and a reading square compose through the natural pullback
comparison. The functor arguments keep all source and target objects explicit. -/
lemma purity_reading_composition
    {C₀ C D₀ D : Type*} [Category C₀] [Category C] [Category D₀] [Category D]
    (P : C₀ ⥤ C) (F₀ : C₀ ⥤ D₀) (F : C ⥤ D) (Q : D₀ ⥤ D)
    (α : P ⋙ F ≅ F₀ ⋙ Q)
    {A B : C₀} {V W R S : C} {T₀ : D₀} {T : D}
    (u : P.obj A ⟶ V) (v : V ⟶ W) (rX : W ≅ S) (rY : A ≅ B)
    (q₁ : P.obj B ⟶ R) (q₂ : R ⟶ S)
    (bX : F.obj S ≅ T) (bY : F₀.obj B ≅ T₀) (w : Q.obj T₀ ⟶ T)
    (hred : u ≫ v ≫ rX.hom = P.map rY.hom ≫ q₁ ≫ q₂)
    (hread : F.map q₁ ≫ F.map q₂ ≫ bX.hom =
      α.hom.app B ≫ Q.map bY.hom ≫ w) :
    F.map u ≫ F.map v ≫ (F.mapIso rX ≪≫ bX).hom =
      α.hom.app A ≫ Q.map (F₀.mapIso rY ≪≫ bY).hom ≫ w := by
  have hm := congrArg F.map hred
  have hn := α.hom.naturality rY.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc] at hm
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hm, hread, reassoc_of% hn]

end CategoryTheory
