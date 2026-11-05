/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Component formulas for mates -/

@[expose] public section

namespace CategoryTheory

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  {G : C ⥤ C'} {H : D ⥤ D'}

/-- A mate is the unit, followed by the square and the counit. -/
lemma projection_mateEquiv_app (a : L ⊣ R) (b : L' ⊣ R')
    (α : TwoSquare G L L' H) (M : D) :
    (mateEquiv a b α).app M = b.unit.app (G.obj (R.obj M)) ≫
      R'.map (α.app (R.obj M)) ≫ R'.map (H.map (a.counit.app M)) := by
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
    Category.comp_id]

end CategoryTheory
