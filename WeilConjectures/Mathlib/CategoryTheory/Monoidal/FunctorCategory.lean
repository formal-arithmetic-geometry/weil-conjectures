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

Similarly, whiskering on the right with a (lax) braided functor `L : D ⥤ E` is (lax)
braided for the pointwise braidings.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Monoidal

variable [MonoidalCategory.{v₂} D] [BraidedCategory.{v₂} D]

@[simp]
theorem braiding_hom_app {F G : C ⥤ D} {X : C} :
    (β_ F G).hom.app X = (β_ (F.obj X) (G.obj X)).hom :=
  rfl

@[simp]
theorem braiding_inv_app {F G : C ⥤ D} {X : C} :
    (β_ F G).inv.app X = (β_ (F.obj X) (G.obj X)).inv :=
  rfl

end Monoidal

namespace Functor

/-- Precomposition with a functor is braided for the pointwise braidings on the
functor categories. -/
instance Braided.whiskeringLeft (E : Type u₃) [Category.{v₃} E] [MonoidalCategory E]
    [BraidedCategory E] (F : C ⥤ D) :
    ((whiskeringLeft C D E).obj F).Braided where
  braided G H := by
    ext X
    exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Whiskering on the right with a lax braided functor is lax braided for the pointwise
braidings on the functor categories. -/
instance LaxBraided.whiskeringRight (E : Type u₃) [Category.{v₃} E] [MonoidalCategory D]
    [MonoidalCategory E] [BraidedCategory D] [BraidedCategory E] (L : D ⥤ E) [L.LaxBraided] :
    ((whiskeringRight C D E).obj L).LaxBraided where
  braided G H := by ext X; exact Functor.LaxBraided.braided _ _

/-- Whiskering on the right with a braided functor is braided for the pointwise braidings
on the functor categories. -/
instance Braided.whiskeringRight (E : Type u₃) [Category.{v₃} E] [MonoidalCategory D]
    [MonoidalCategory E] [BraidedCategory D] [BraidedCategory E] (L : D ⥤ E) [L.Braided] :
    ((whiskeringRight C D E).obj L).Braided where
  braided G H := by ext X; exact Functor.LaxBraided.braided _ _

end Functor

end CategoryTheory
