/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates and whiskering of the vertical sides of a `2`-square

`Mathlib.CategoryTheory.Adjunction.Mates` records how the mates correspondence interacts
with whiskering the two *horizontal* sides of a square, which are the functors carrying the
adjunctions (`CategoryTheory.mateEquiv_conjugateEquiv_vcomp` and
`CategoryTheory.conjugateEquiv_mateEquiv_vcomp`, where the whiskering has to be replaced by
the conjugate transformation). Whiskering the two *vertical* sides is simpler: the mate is
whiskered by the very same transformation, since no adjunction is transported.

## Main results

- `CategoryTheory.mateEquiv_whiskerTop` and `CategoryTheory.mateEquiv_whiskerBottom`.
-/

@[expose] public section

set_option maxRecDepth 4000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category Functor Adjunction

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
variable {G G' : C ⥤ E} {H H' : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mate of a square whiskered by a transformation of its top side is the mate
whiskered by the same transformation, now on the right side. -/
theorem mateEquiv_whiskerTop (α : TwoSquare G' L₁ L₂ H) (c : G ⟶ G') :
    mateEquiv adj₁ adj₂ (α.whiskerTop c) = (mateEquiv adj₁ adj₂ α).whiskerRight c := by
  ext b
  simp [mateEquiv]

/-- The mate of a square whiskered by a transformation of its bottom side is the mate
whiskered by the same transformation, now on the left side. -/
theorem mateEquiv_whiskerBottom (α : TwoSquare G L₁ L₂ H) (d : H ⟶ H') :
    (mateEquiv adj₁ adj₂ (α.whiskerBottom d)).natTrans =
      (mateEquiv adj₁ adj₂ α).natTrans ≫ Functor.whiskerRight d R₂ := by
  ext b
  simp only [mateEquiv, Equiv.coe_fn_mk, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_id, Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    Category.assoc, Functor.comp_map, ← R₂.map_comp, d.naturality]

end CategoryTheory
