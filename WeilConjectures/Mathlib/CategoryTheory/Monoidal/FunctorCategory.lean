/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# The precomposition functor is braided

When `E` is a braided monoidal category, the functor categories `C ⥤ E` and `D ⥤ E` carry
the pointwise braiding `Monoidal.functorCategoryBraided`, and precomposition with any
functor `F : C ⥤ D` is strong monoidal with identity structure maps
(`Functor.Monoidal.whiskeringLeft`). We record that this monoidal structure preserves the
pointwise braiding: `((whiskeringLeft C D E).obj F).Braided`.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor

/-- Precomposition with a functor is braided for the pointwise braidings on the
functor categories. -/
instance Braided.whiskeringLeft (E : Type u₃) [Category.{v₃} E] [MonoidalCategory E]
    [BraidedCategory E] (F : C ⥤ D) :
    ((whiskeringLeft C D E).obj F).Braided where
  braided G H := by
    ext X
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end Functor

end CategoryTheory
