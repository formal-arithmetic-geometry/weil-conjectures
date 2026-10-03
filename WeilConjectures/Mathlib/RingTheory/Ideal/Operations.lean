/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# The order of an element with respect to an ideal

An element not in `⋂ₙ Iⁿ` lies in some `I ^ r` but not in `I ^ (r + 1)`.
-/

@[expose] public section

variable {A : Type*} [CommRing A] {I : Ideal A}

namespace Ideal

/-- If `a ∉ ⋂ₙ Iⁿ`, then `a` has a well-defined `I`-adic order. -/
theorem exists_mem_pow_notMem_pow_succ_of_notMem_iInf {a : A} (h : a ∉ ⨅ r : ℕ, I ^ r) :
    ∃ r, a ∈ I ^ r ∧ a ∉ I ^ (r + 1) := by
  rw [Submodule.mem_iInf, not_forall] at h
  obtain ⟨n, hn⟩ := h
  induction n with
  | zero => simp at hn
  | succ n ih =>
    by_cases h : a ∈ I ^ n
    exacts [⟨n, h, hn⟩, ih h]

end Ideal
