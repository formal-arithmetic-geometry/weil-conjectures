/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# Idempotents in the Jacobson radical

An idempotent element of the Jacobson radical of a commutative ring is zero
(`IsIdempotentElem.eq_zero_of_mem_jacobson`).
-/

@[expose] public section

/-- An idempotent in the Jacobson radical is zero. -/
theorem IsIdempotentElem.eq_zero_of_mem_jacobson {S : Type*} [CommRing S] {e : S}
    (he : IsIdempotentElem e) (h : e ∈ Ring.jacobson S) : e = 0 := by
  have hu : IsUnit (1 - e) := by
    by_contra hcon
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {1 - e})
      (fun htop ↦ hcon (Ideal.span_singleton_eq_top.mp htop))
    have h1 : (1 : S) - e ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : e ∈ M := Ring.jacobson_le_of_isMaximal M h
    exact hM.ne_top (Ideal.eq_top_iff_one M |>.mpr (by simpa using M.add_mem h1 h2))
  have hz : e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, he.eq, sub_self]
  exact (hu.mul_left_eq_zero).mp hz
