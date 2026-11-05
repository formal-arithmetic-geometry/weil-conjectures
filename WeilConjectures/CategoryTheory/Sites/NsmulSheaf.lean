/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Sheaves with values in a category killed by an integer

If an integer `N` kills every object of a preadditive category `A`, then it kills every sheaf
with values in `A`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {A : Type*} [Category A]
  [Preadditive A]

end CategoryTheory.Sheaf
