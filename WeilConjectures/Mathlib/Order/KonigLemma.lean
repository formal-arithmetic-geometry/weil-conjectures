/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Order.KonigLemma

/-!
# Lifting through a tower of surjections

A tower `… → M 2 → M 1 → M 0` of surjections admits a compatible family of elements with any
prescribed term at level zero: one lifts through the tower step by step.

This is the surjective counterpart of `exists_seq_forall_proj_of_forall_finite`, the formulation
of Kőnig's infinity lemma for a tower whose transition maps have finite fibres, and it is stated
in the mirror of that file for that reason.

## Main statements

- `exists_seq_of_forall_surjective`
-/

@[expose] public section

/-- **A tower of surjections admits a compatible family with a prescribed level-zero term.**
Given surjections `φ n : M (n + 1) → M n` and an element `a` of `M 0`, there is a family
`s n : M n` with `s 0 = a` and `φ n (s (n + 1)) = s n` for every `n`. -/
theorem exists_seq_of_forall_surjective {M : ℕ → Type*} (φ : ∀ n : ℕ, M (n + 1) → M n)
    (hφ : ∀ n : ℕ, Function.Surjective (φ n)) (a : M 0) :
    ∃ s : ∀ n : ℕ, M n, s 0 = a ∧ ∀ n : ℕ, φ n (s (n + 1)) = s n :=
  ⟨fun n ↦ Nat.rec a (fun k sk ↦ Function.surjInv (hφ k) sk) n, rfl,
    fun n ↦ Function.surjInv_eq (hφ n) _⟩
