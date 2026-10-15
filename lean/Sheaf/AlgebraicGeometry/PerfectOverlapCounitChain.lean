/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-! # Counit naturality for a chain of local comparison maps -/

@[expose] public section

open CategoryTheory
namespace AlgebraicGeometry

/-- A chain mapped through an inverse equivalence leaves the site via its
counit as the same chain in the target category.

Proof: Functoriality combines the five inverse images into the image of their
composite. Naturality of the equivalence counit moves that composite past the
counit. Applying the final functor and expanding its map of the composite gives
the displayed chain. This is the categorical part of the open-site comparison
in Stacks Project, Tags 08BV and 08DW. -/
theorem equivalence_counit_five
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (e : C ≌ D) (cart : D ⥤ E)
    {A B F G H I : D}
    (a : A ⟶ B) (b : B ⟶ F) (c : F ⟶ G) (d : G ⟶ H) (f : H ⟶ I) :
    (e.functor ⋙ cart).map (e.inverse.map a) ≫
        (e.functor ⋙ cart).map (e.inverse.map b) ≫
          (e.functor ⋙ cart).map (e.inverse.map c) ≫
            (e.functor ⋙ cart).map (e.inverse.map d) ≫
              (e.functor ⋙ cart).map (e.inverse.map f) ≫
                cart.map (e.counitIso.hom.app I) =
      cart.map (e.counitIso.hom.app A) ≫
        cart.map a ≫ cart.map b ≫ cart.map c ≫ cart.map d ≫ cart.map f := by
  have hn := e.counitIso.hom.naturality (a ≫ b ≫ c ≫ d ≫ f)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hc := congrArg cart.map hn
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using hc

end AlgebraicGeometry
