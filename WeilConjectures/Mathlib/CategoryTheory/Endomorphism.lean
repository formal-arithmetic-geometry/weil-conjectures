/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Endomorphism

/-!
# Powers of intertwined endomorphisms

A morphism `p : Y ⟶ X` intertwining endomorphisms `a` of `Y` and `b` of `X`
(`a ≫ p = p ≫ b`) intertwines their powers in the endomorphism monoids.

## Main statements

- `CategoryTheory.End.asHom_pow_comp_eq_comp_asHom_pow`: `a ^ m ≫ p = p ≫ b ^ m`.
-/

@[expose] public section

namespace CategoryTheory.End

variable {C : Type*} [Category* C] {X Y : C}

/-- A morphism `p` intertwining endomorphisms `a` and `b` (`a ≫ p = p ≫ b`) intertwines their
`m`-th powers. -/
lemma asHom_pow_comp_eq_comp_asHom_pow {a : Y ⟶ Y} {b : X ⟶ X} {p : Y ⟶ X}
    (h : a ≫ p = p ≫ b) (m : ℕ) :
    asHom (of a ^ m) ≫ p = p ≫ asHom (of b ^ m) := by
  induction m with
  | zero => simp [one_def]
  | succ m ih =>
    change asHom (of a ^ m * of a) ≫ p = p ≫ asHom (of b ^ m * of b)
    rw [mul_def, mul_def]
    change (a ≫ asHom (of a ^ m)) ≫ p = p ≫ b ≫ asHom (of b ^ m)
    rw [Category.assoc, ih, reassoc_of% h]

end CategoryTheory.End
