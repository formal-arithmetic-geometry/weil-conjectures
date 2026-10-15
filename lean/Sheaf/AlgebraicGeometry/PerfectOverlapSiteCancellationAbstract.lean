/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

open CategoryTheory
namespace AlgebraicGeometry

/-- A return unit followed by an equivalence counit cancels across any comparison.
Proof: The triangle identity identifies the image of the inverse unit with
the counit on the image object. Naturality moves that counit across the
comparison isomorphism, whose inverse then cancels. -/
theorem equivalence_return_cancel
    {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) (M : C) (N : D) (α : N ≅ e.functor.obj M) :
    e.functor.map (e.inverse.map α.hom) ≫
      e.functor.map (e.unitIso.inv.app M) ≫
        e.functor.map (𝟙 M) ≫ α.inv = e.counitIso.hom.app N := by
  have hε : e.functor.map (e.unitIso.inv.app M) =
      e.counitIso.hom.app (e.functor.obj M) := by
    apply (cancel_epi (e.functor.map (e.unitIso.hom.app M))).1
    calc
      e.functor.map (e.unitIso.hom.app M) ≫
          e.functor.map (e.unitIso.inv.app M) = 𝟙 _ := by
        rw [← e.functor.map_comp, Iso.hom_inv_id_app, e.functor.map_id]
      _ = e.functor.map (e.unitIso.hom.app M) ≫
          e.counitIso.hom.app (e.functor.obj M) :=
        (e.functor_unitIso_comp M).symm
  have hn := e.counitIso.hom.naturality α.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hId : e.functor.map (𝟙 M) = 𝟙 (e.functor.obj M) := e.functor.map_id M
  rw [hε, hId]
  have hdrop :
      (e.functor.map (e.inverse.map α.hom) ≫
        e.counitIso.hom.app (e.functor.obj M)) ≫ 𝟙 (e.functor.obj M) =
        e.functor.map (e.inverse.map α.hom) ≫
          e.counitIso.hom.app (e.functor.obj M) := Category.comp_id _
  simp only [← Category.assoc]
  rw [hdrop, hn]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry
