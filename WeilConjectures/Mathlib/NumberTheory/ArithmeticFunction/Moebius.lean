/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

@[expose] public section

/-!
# Möbius inversion of a degree-weighted divisor sum

The counting functions of this development all have the shape
`c n = ∑_{m ∣ n} m * a m`, with `a m` a number of objects of degree `m`. This file records
the Möbius inversion of that relation, which recovers `a` from `c`.

## Main results

- `ArithmeticFunction.sum_divisors_moebius_mul_eq_mul`
-/

namespace ArithmeticFunction

/-- **Möbius inversion of a degree-weighted divisor sum.** If `c n = ∑_{k ∣ n} k * a k`
for every divisor `n ≥ 1` of `m`, then `∑_{r ∣ m} μ r * c (m / r) = m * a m`; in
particular `m` divides the left hand side.
(blueprint: `lemma:weil-moebius-inversion-degree-weighted`) -/
theorem sum_divisors_moebius_mul_eq_mul {c a : ℕ → ℕ} {m : ℕ} (hm : m ≠ 0)
    (hc : ∀ n, n ≠ 0 → n ∣ m → c n = ∑ k ∈ n.divisors, k * a k) :
    ∑ r ∈ m.divisors, (moebius r : ℤ) * c (m / r) = (m : ℤ) * a m := by
  have hclosed : ∀ k l : ℕ, k ∣ l → l ∈ {k | k ∣ m} → k ∈ {k | k ∣ m} :=
    fun _ _ hkl hl ↦ hkl.trans hl
  have hsum : ∀ k : ℕ, 0 < k → k ∈ {k | k ∣ m} →
      ∑ i ∈ k.divisors, ((i : ℤ) * (a i : ℤ)) = (c k : ℤ) := by
    intro k hk hkm
    exact_mod_cast (congrArg (fun j : ℕ ↦ (j : ℤ)) (hc k hk.ne' hkm)).symm
  have key := (sum_eq_iff_sum_mul_moebius_eq_on (R := ℤ)
    (f := fun i ↦ (i : ℤ) * (a i : ℤ)) (g := fun k ↦ (c k : ℤ)) _ hclosed).mp hsum m
    (Nat.pos_of_ne_zero hm) dvd_rfl
  simp only [Int.cast_id] at key
  rw [← Nat.sum_divisorsAntidiagonal fun r s ↦ (moebius r : ℤ) * (c s : ℤ)]
  exact key

end ArithmeticFunction

end
