/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Minimal primes of reduced rings

- `IsReduced.eq_zero_of_forall_mem_minimalPrimes`: in a reduced ring, an element lying in every
  minimal prime is zero.
-/

@[expose] public section

/-- In a reduced ring, an element lying in every minimal prime is zero: the intersection of the
minimal primes is the nilradical. -/
lemma IsReduced.eq_zero_of_forall_mem_minimalPrimes {A : Type*} [CommRing A] [IsReduced A]
    {x : A} (hx : ∀ q ∈ minimalPrimes A, x ∈ q) : x = 0 := by
  have : x ∈ (⊥ : Ideal A).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.2 hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 this
  exact IsReduced.eq_zero x ⟨n, Ideal.mem_bot.1 hn⟩
