/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Derivations and squares of ideals

A derivation maps the square of an ideal into the ideal itself, so it descends to a map
`I ⧸ I ^ 2 → M ⧸ I • M`.  Only the first statement is recorded here.
-/

@[expose] public section

/-- A derivation maps `I ^ 2` into `I`: this is the Leibniz rule together with `I * I ≤ I`. -/
theorem Ideal.derivation_mem_of_mem_sq {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (I : Ideal A) {x : A} (hx : x ∈ I ^ 2) : D x ∈ I := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun m hm n hn ↦ ?_) fun x y hx hy ↦ ?_
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact I.add_mem (I.mul_mem_right _ hm) (I.mul_mem_right _ hn)
  · simpa using I.add_mem hx hy
