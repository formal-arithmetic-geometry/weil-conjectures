/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additive functors and morphisms out of biproducts

For an additive functor `G`, the image of a morphism `⨁ f ⟶ Y` with components `g j` is an
isomorphism if and only if the morphism `⨁ G (f j) ⟶ G Y` with components `G (g j)` is one
(`CategoryTheory.Functor.isIso_map_biproduct_desc_iff`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D] (G : C ⥤ D)
  [G.Additive] {J : Type} [Finite J] {f : J → C} [HasBiproduct f] {Y : C} (g : ∀ j, f j ⟶ Y)

/-- For an additive functor `G`, the image `G (⨁ f) ⟶ G Y` of the morphism out of a biproduct
with components `g j` is an isomorphism if and only if the morphism `⨁ G (f j) ⟶ G Y` with
components `G (g j)` is. -/
lemma isIso_map_biproduct_desc_iff :
    IsIso (G.map (biproduct.desc g)) ↔ IsIso (biproduct.desc fun j ↦ G.map (g j)) := by
  have := Fintype.ofFinite J
  have h : (biproduct.desc fun j ↦ G.map (g j)) =
      (G.mapBiproduct f).inv ≫ G.map (biproduct.desc g) :=
    biproduct.hom_ext' _ _ fun j ↦ by simp [← G.map_comp]
  rw [h, isIso_comp_left_iff]

end CategoryTheory.Functor
