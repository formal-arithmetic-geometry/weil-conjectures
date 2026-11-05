/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Inverting the horizontal maps of a comparison square -/

@[expose] public section

namespace CategoryTheory

lemma purity_inverse_square {C : Type*} [Category C]
    {A B A' B' : C} (i : A ≅ B) (j : A' ≅ B')
    (u : A ⟶ A') (v : B ⟶ B') (h : u ≫ j.hom = i.hom ≫ v) :
    i.inv ≫ u = v ≫ j.inv := by
  apply (cancel_mono j.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, h,
    Iso.inv_hom_id_assoc]

/-- Cancel a leading compositor without expanding a concrete category instance. -/
lemma purity_factor_from_compositor {C : Type*} [Category C]
    {A B T : C} (i : A ≅ B) (v : B ⟶ T) (w : A ⟶ T)
    (h : i.hom ≫ v = w) : v = i.inv ≫ w := by
  rw [← h, Iso.inv_hom_id_assoc]

end CategoryTheory
