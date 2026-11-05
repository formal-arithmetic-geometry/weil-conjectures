/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Transporting a unit datum from pullback to inverse pushforward -/

@[expose] public section

namespace CategoryTheory

/-- A comparison that preserves a specified unit map continues to do so after
replacing either endofunctor by an isomorphic one. -/
lemma purity_unitDatum_transport
    {C D : Type*} [Category C] [Category D]
    (E : C ⥤ D) (A B : C ⥤ C) (A' B' : D ⥤ D)
    (cA : E ⋙ A' ≅ A ⋙ E) (cB : E ⋙ B' ≅ B ⋙ E)
    (i : A ≅ B) (j : A' ≅ B') {M : C} {U : D} (e : E.obj M ≅ U)
    (a : A.obj M ⟶ M) (b : B.obj M ⟶ M) (u : A'.obj U ⟶ U)
    (hc : cA.hom.app M = j.hom.app (E.obj M) ≫ cB.hom.app M ≫ E.map (i.inv.app M))
    (hab : i.hom.app M ≫ b = a)
    (hu : A'.map e.inv ≫ cA.hom.app M ≫ E.map a ≫ e.hom = u) :
    B'.map e.inv ≫ cB.hom.app M ≫ E.map b ≫ e.hom = j.inv.app U ≫ u := by
  rw [hc, ← hab, E.map_comp] at hu
  simp only [Category.assoc] at hu
  rw [← E.map_comp_assoc, Iso.inv_hom_id_app, E.map_id, Category.id_comp] at hu
  apply (cancel_epi (j.hom.app U)).mp
  rw [Iso.hom_inv_id_app_assoc, ← j.hom.naturality_assoc]
  exact hu

end CategoryTheory
