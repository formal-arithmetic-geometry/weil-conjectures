/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Precomposition on functor categories is braided

The functor category `C ⥤ E` is monoidal (resp. braided, symmetric) whenever `E` is, with all
the structure defined pointwise. Precomposition with a functor `F : C ⥤ D` is strong monoidal
by `CategoryTheory.Functor.Monoidal.whiskeringLeft`; here we record that it is moreover braided.
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

/-- Precomposition with a functor `F : C ⥤ D` is a braided functor `(D ⥤ E) ⥤ (C ⥤ E)`. -/
instance Functor.Braided.whiskeringLeft (E : Type*) [Category* E] [MonoidalCategory E]
    [BraidedCategory E] (F : C ⥤ D) : ((whiskeringLeft _ _ E).obj F).Braided where
  braided X Y := by
    ext c
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end CategoryTheory
