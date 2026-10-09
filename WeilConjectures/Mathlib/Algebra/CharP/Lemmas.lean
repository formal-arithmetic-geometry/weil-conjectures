/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Frobenius powers in rings in which a prime vanishes

Mathlib's `iterateFrobenius R p n` needs `ExpChar R p`, which fails for the zero ring. Rings of
sections of a scheme of characteristic `p` may be zero (over the empty open), so this file
provides the ring endomorphism `x ↦ x ^ p ^ n` under the weaker hypothesis `(p : R) = 0`.

## Main definitions

- `powPrimePowRingHom`: the ring endomorphism `x ↦ x ^ p ^ n` of a commutative ring in which the
  prime `p` vanishes.
-/

@[expose] public section

/-- In a commutative ring in which a prime `p` vanishes, `x ↦ x ^ p ^ n` is additive. -/
theorem add_pow_prime_pow_of_natCast_eq_zero {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) (n : ℕ) (x y : R) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  · have : Fact p.Prime := ⟨hp⟩
    have : CharP R p := (CharP.charP_iff_prime_eq_zero hp).mpr h
    exact add_pow_char_pow x y p n

/-- The ring endomorphism `x ↦ x ^ p ^ n` of a commutative ring in which the prime `p`
vanishes. -/
def powPrimePowRingHom (R : Type*) [CommRing R] {p : ℕ} (hp : p.Prime) (h : (p : R) = 0)
    (n : ℕ) : R →+* R where
  toFun x := x ^ p ^ n
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero _ hp.ne_zero)
  map_add' := add_pow_prime_pow_of_natCast_eq_zero hp h n

@[simp]
theorem powPrimePowRingHom_apply (R : Type*) [CommRing R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) (n : ℕ) (x : R) : powPrimePowRingHom R hp h n x = x ^ p ^ n := rfl
