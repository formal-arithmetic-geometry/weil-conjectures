/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Binomial

/-!
# Binomial coefficients in a binomial ring as products

`Ring.choose r n` is defined through `descPochhammer`. We record the resulting closed formula
`n ! * Ring.choose r n = ∏ j ∈ Finset.range n, (r - j)` and, over a field of characteristic zero,
the division form of it. The latter is what turns `m ↦ Ring.choose m n` into the evaluation of an
explicit polynomial of degree `n`.
-/

@[expose] public section

open Finset Nat Polynomial

namespace Ring

private lemma smeval_descPochhammer_eq_prod_range {R : Type*} [CommRing R] (n : ℕ) (r : R) :
    (descPochhammer ℤ n).smeval r = ∏ j ∈ range n, (r - j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_right, smeval_mul, ih, prod_range_succ, smeval_sub, smeval_X,
      smeval_natCast]
    simp

/-- The closed formula for the binomial coefficients of a binomial ring: `n !` times
`Ring.choose r n` is the product of the `r - j` for `j < n`. -/
theorem factorial_mul_choose_eq_prod_range {R : Type*} [CommRing R] [BinomialRing R]
    (r : R) (n : ℕ) : (n ! : R) * choose r n = ∏ j ∈ range n, (r - j) := by
  rw [← nsmul_eq_mul, ← descPochhammer_eq_factorial_smul_choose,
    smeval_descPochhammer_eq_prod_range]

/-- Over a field of characteristic zero the binomial coefficient `Ring.choose r n` is the product
of the `r - j` for `j < n`, divided by `n !`. -/
theorem choose_eq_inv_factorial_mul_prod_range {K : Type*} [Field K] [CharZero K] (x : K)
    (n : ℕ) : choose x n = (n ! : K)⁻¹ * ∏ j ∈ range n, (x - j) := by
  rw [← factorial_mul_choose_eq_prod_range, inv_mul_cancel_left₀]
  exact_mod_cast Nat.cast_ne_zero.mpr n.factorial_ne_zero

/-- Binomial coefficients of integers are compatible with the ring homomorphism `ℤ → R`. -/
@[simp, norm_cast]
theorem choose_intCast {R : Type*} [Ring R] [BinomialRing R] (m : ℤ) (n : ℕ) :
    ((choose m n : ℤ) : R) = choose (m : R) n := by
  simpa using map_choose (Int.castRingHom R) m n

end Ring
