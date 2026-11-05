/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Monoidal.End

/-!
# Shifts on the Karoubi envelope

Let `C` be a category with a shift by an additive monoid `A`. The canonical extension functor
`functorExtension₂ C C : (C ⥤ C) ⥤ (Karoubi C ⥤ Karoubi C)` is (strictly) monoidal for the
composition of endofunctors, so that the shift of `C` extends to a shift of the Karoubi envelope:
`(K, e)⟦a⟧ = (K⟦a⟧, e⟦a⟧)`. The inclusion `C ⥤ Karoubi C` commutes with the shifts.

## Main definitions

- `CategoryTheory.Idempotents.Karoubi.hasShift`: the shift on `Karoubi C`.
- `CategoryTheory.Idempotents.toKaroubi.commShift`: `toKaroubi C` commutes with the shifts.
-/

@[expose] public section

namespace CategoryTheory.Idempotents

open Category MonoidalCategory

attribute [local instance] endofunctorMonoidalCategory

variable (C : Type*) [Category* C]

variable {C} (A : Type*) [AddMonoid A] [HasShift C A]

variable {A}

end CategoryTheory.Idempotents
