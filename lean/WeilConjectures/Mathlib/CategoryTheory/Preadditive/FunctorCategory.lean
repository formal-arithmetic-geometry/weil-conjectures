/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Limits of integer multiples of natural transformations

The morphism of limits induced by `n • α` is `n • limMap α` (`CategoryTheory.limMap_zsmul`).
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {J C : Type*} [Category J] [Category C] [Preadditive C]

/-- The morphism of limits induced by `n • α` is `n` times the morphism induced by `α`. -/
@[simp]
lemma limMap_zsmul {F G : J ⥤ C} [HasLimit F] [HasLimit G] (n : ℤ) (α : F ⟶ G) :
    limMap (n • α) = n • limMap α :=
  limit.hom_ext fun j ↦ by
    rw [limMap_π, NatTrans.app_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp, limMap_π]

end CategoryTheory
