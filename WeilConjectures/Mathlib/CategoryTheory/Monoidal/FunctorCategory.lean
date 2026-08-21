/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Precomposition is a braided functor for the pointwise monoidal structures

When `E` is a braided monoidal category, the functor categories `C ⥤ E` and `D ⥤ E`
carry pointwise braided monoidal structures, and precomposition with any functor
`F : C ⥤ D` is a braided functor: its structure morphisms are identities and the
braiding is computed objectwise.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Precomposition with any functor is a braided functor for the pointwise braided
monoidal structures on the functor categories. -/
instance Functor.Braided.whiskeringLeft (E : Type u₃) [Category.{v₃} E]
    [MonoidalCategory E] [BraidedCategory E] (F : C ⥤ D) :
    ((whiskeringLeft C D E).obj F).Braided where
  braided X Y := by
    ext c
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end CategoryTheory
