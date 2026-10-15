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

/-- Paste a two-step return triangle with its terminal cancellation.
The proof is associativity followed by the two supplied equations. -/
theorem paste_return_triangle
    {C : Type*} [Category* C] {A B D E F G : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ G}
    {p : A ⟶ E} {q : E ⟶ F} {r : F ⟶ D} {s : F ⟶ G}
    (htriangle : a ≫ b = p ≫ q ≫ r) (hcancel : r ≫ c = s) :
    a ≫ b ≫ c = p ≫ q ≫ s := by
  calc
    a ≫ b ≫ c = (a ≫ b) ≫ c := (Category.assoc a b c).symm
    _ = (p ≫ q ≫ r) ≫ c := congrArg (fun z ↦ z ≫ c) htriangle
    _ = p ≫ q ≫ (r ≫ c) := by simp only [Category.assoc]
    _ = p ≫ q ≫ s := by rw [hcancel]

/-- An equivalence counit is invariant under transport to an isomorphic object.
Proof: Naturality of the counit moves the isomorphism through the counit;
its inverse then cancels. This is the object-level cancellation for nested
open restrictions after the first return triangle. -/
theorem equivalence_counit_transport_cancel
    {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) {X Y : D} (α : X ≅ Y) :
    e.functor.map (e.inverse.map α.hom) ≫ e.counitIso.hom.app Y ≫ α.inv =
      e.counitIso.hom.app X := by
  have hn := e.counitIso.hom.naturality α.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry
