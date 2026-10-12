/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Idempotents in local rings and in the Jacobson radical

In a local ring, the only idempotent elements are `0` and `1`.
More generally, any idempotent lying in the Jacobson radical of an arbitrary
commutative ring must be zero.
-/

@[expose] public section

/-- An idempotent element of a commutative ring that lies in the Jacobson radical
(of the zero ideal) is zero. -/
lemma IsIdempotentElem.eq_zero_of_mem_jacobson_bot {R : Type*} [CommRing R]
    {e : R} (he : IsIdempotentElem e) (hmem : e ∈ Ideal.jacobson (⊥ : Ideal R)) :
    e = 0 := by
  rw [Ideal.mem_jacobson_bot] at hmem
  have hu : IsUnit (1 - e) := by simpa [mul_neg_one, neg_add_eq_sub] using hmem (-1)
  exact hu.mul_left_eq_zero.mp he.mul_one_sub_self

/-- In a local ring, every idempotent element is `0` or `1`. -/
lemma IsIdempotentElem.eq_zero_or_one_of_isLocalRing {R : Type*} [CommRing R]
    [IsLocalRing R] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases Classical.em (e ∈ IsLocalRing.maximalIdeal R) with hmem | hnmem
  · exact .inl <| he.eq_zero_of_mem_jacobson_bot <| by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  · rw [IsLocalRing.notMem_maximalIdeal] at hnmem
    exact .inr (sub_eq_zero.mp (hnmem.mul_right_eq_zero.mp he.mul_one_sub_self)).symm

/-- Idempotents are determined modulo the Jacobson radical: two idempotents whose difference
lies in the Jacobson radical are equal, since `e (1 - e')` and `e' (1 - e)` are idempotents in
the Jacobson radical. (blueprint: `lem-weil-pbc-idempotents-determined-modulo-radical`) -/
lemma IsIdempotentElem.eq_of_sub_mem_jacobson_bot {R : Type*} [CommRing R] {e e' : R}
    (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : e - e' ∈ Ideal.jacobson (⊥ : Ideal R)) : e = e' := by
  have h' : e' - e ∈ Ideal.jacobson (⊥ : Ideal R) := by rw [← neg_sub]; exact neg_mem h
  have h₁ : e * (1 - e') = 0 := (he.mul he'.one_sub).eq_zero_of_mem_jacobson_bot <| by
    have : e * (1 - e') = e * (e - e') := by rw [mul_sub, mul_sub, mul_one, he.eq]
    rw [this]
    exact Ideal.mul_mem_left _ _ h
  have h₂ : e' * (1 - e) = 0 := (he'.mul he.one_sub).eq_zero_of_mem_jacobson_bot <| by
    have : e' * (1 - e) = e' * (e' - e) := by rw [mul_sub, mul_sub, mul_one, he'.eq]
    rw [this]
    exact Ideal.mul_mem_left _ _ h'
  linear_combination h₁ - h₂
