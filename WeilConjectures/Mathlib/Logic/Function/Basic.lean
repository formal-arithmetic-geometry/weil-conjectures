/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic

/-!
# Lifting through a tower of surjections

A tower `… ⟶ M 2 ⟶ M 1 ⟶ M 0` of surjections admits a compatible family of elements with any
prescribed term at level zero: one lifts through the tower step by step.
-/

@[expose] public section

namespace Function

/-- **A tower of surjections admits a compatible family with a prescribed level-zero term.**
Given surjections `φ n : M (n + 1) → M n` and an element `a` of `M 0`, there is a family
`s n : M n` with `s 0 = a` and `φ n (s (n + 1)) = s n` for every `n`. -/
theorem exists_seq_of_forall_surjective {M : ℕ → Type*} (φ : ∀ n : ℕ, M (n + 1) → M n)
    (hφ : ∀ n : ℕ, Surjective (φ n)) (a : M 0) :
    ∃ s : ∀ n : ℕ, M n, s 0 = a ∧ ∀ n : ℕ, φ n (s (n + 1)) = s n :=
  ⟨fun n ↦ Nat.rec a (fun k sk ↦ surjInv (hφ k) sk) n, rfl, fun n ↦ surjInv_eq (hφ n) _⟩

end Function
