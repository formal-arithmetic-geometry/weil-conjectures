/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Detecting a non-zero value through a factorisation

If a composite `α ≫ β` of morphisms of abelian groups takes a non-zero value at `x`, then already
`α` takes a non-zero value at `x`.

## Main statements

- `AddCommGrpCat.apply_ne_zero_of_comp_apply_ne_zero`
-/

@[expose] public section

open CategoryTheory

universe u

namespace AddCommGrpCat

/-- If a composite of morphisms of abelian groups does not vanish at `x`, then neither does its
first factor:

```
       α         β
  A ──────> B ──────> C
```
-/
theorem apply_ne_zero_of_comp_apply_ne_zero {A B C : AddCommGrpCat.{u}} (α : A ⟶ B) (β : B ⟶ C)
    {x : A} (hx : (α ≫ β) x ≠ 0) : α x ≠ 0 := fun h0 ↦ hx <| by
  rw [ConcreteCategory.comp_apply, h0, map_zero]

end AddCommGrpCat
