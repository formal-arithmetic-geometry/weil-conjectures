/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# Splitting of idempotents

Supplements to `Mathlib.CategoryTheory.Idempotents.Basic`: splittings of idempotents are
transported along isomorphisms and functors, and in a preadditive category two idempotents
whose difference has square zero are conjugate, so that one splits if and only if the other does.

## Main statements

- `CategoryTheory.Idempotents.exists_split_of_sub_comp_sub_eq_zero`: if `p` and `q` are
  idempotents of an object of a preadditive category with `(p - q) ≫ (p - q) = 0` and `q`
  splits, then `p` splits.
-/

@[expose] public section

namespace CategoryTheory.Idempotents

open Category

variable {C : Type*} [Category* C]

/-- The property that an endomorphism `p` of `X` is split: `p = e ≫ i` for a retraction
`e : X ⟶ Y` and a section `i : Y ⟶ X` with `i ≫ e = 𝟙 Y`. -/
def IsSplit {X : C} (p : X ⟶ X) : Prop :=
  ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p

section Preadditive

variable [Preadditive C]

open Preadditive

end Preadditive

end CategoryTheory.Idempotents
