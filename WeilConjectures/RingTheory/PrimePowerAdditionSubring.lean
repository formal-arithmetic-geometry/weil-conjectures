/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.WittVector.Frobenius
import Mathlib.Tactic.Ring

/-!
# Addition and prime-power subring membership

Source: Stacks Project, Algebra, Tag 0545, `lemma-help-with-powers`, evaluated in an
arbitrary commutative ring (blueprint: lem-pur-prime-power-addition-subring).
-/

@[expose] public section

universe u

namespace Subring

private theorem pow_mod_mul_mem {C : Type u} [CommRing C] (A : Subring C)
    {x c : C} {q : ℕ} (hx : x ^ q ∈ A) (hc : c * x ∈ A) (i : ℕ) :
    c ^ (i % q) * x ^ i ∈ A := by
  have hi : x ^ i = (x ^ q) ^ (i / q) * x ^ (i % q) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    simpa [Nat.add_comm] using (Nat.mod_add_div i q).symm
  have heq : c ^ (i % q) * x ^ i = (x ^ q) ^ (i / q) * (c * x) ^ (i % q) := by
    rw [hi, mul_pow]
    ring
  rw [heq]
  exact A.mul_mem (A.pow_mem hx _) (A.pow_mem hc _)

private theorem pow_dvd_choose_of_mod_ne_zero {p a k t D : ℕ} (hp : p.Prime)
    (hk : k ≤ p ^ a) (hr : k % p ^ t ≠ 0) (hD : D + t ≤ a) :
    p ^ D ∣ (p ^ a).choose k := by
  have : Fact p.Prime := ⟨hp⟩
  have hk0 : 0 < k := by
    by_contra h
    have : k = 0 := by omega
    simp [this] at hr
  have hv : multiplicity p k < t := by
    by_contra h
    have hpow : p ^ t ∣ k := pow_dvd_of_le_multiplicity (by omega)
    exact hr (Nat.mod_eq_zero_of_dvd hpow)
  have hdiv := WittVector.map_frobeniusPoly.key₁ p a (k - 1) (by omega)
  rw [Nat.sub_add_cancel hk0] at hdiv
  exact (pow_dvd_pow p (by omega : D ≤ a - multiplicity p k)).trans hdiv

/-- (blueprint: lem-pur-prime-power-addition-subring) Stacks Project, Algebra, Tag 0545,
`lemma-help-with-powers`, evaluated in a commutative ring. If a unital subring contains
prime-power powers and the corresponding prime-power multiples of `x` and `y`, it contains
such a power and multiple of their sum, with the same positive exponent.

Proof plan:
1. Choose `a = n * p ^ n + m * p ^ m + n + m`. It is positive and at least `n` and `m`.
   Put `B = n * (p ^ n - 1) + m * (p ^ m - 1)`. Both `a - n + 1` and `a - m + 1`
   are at least `B`. The subring contains all integer multiples of `1`, so the identity
   `p^a(x+y) = p^(a-n)(p^n x) + p^(a-m)(p^m y)` gives the required multiple membership.
2. Expand `(x+y)^(p^a)` by `add_pow` (lem-pur-commutative-ring-binomial-expansion).
   For an index `i`, put `j = p^a - i` and write `i = q*p^n + r`, `j = q'*p^m + r'`
   with `r < p^n` and `r' < p^m`. Put `D = n*r + m*r'`, so `D ≤ B`.
3. If both remainders vanish, divisibility of the binomial coefficient by `p^D` is trivial.
   If `r > 0`, then `i > 0` and `v_p(i) ≤ n-1`. Apply
   `WittVector.map_frobeniusPoly.key₁` (lem-pur-prime-power-binomial-divisibility):
   `p^(a-v_p(i))` divides the coefficient, and `D ≤ B ≤ a-n+1 ≤ a-v_p(i)`.
   Otherwise use `j > 0`, `v_p(j) ≤ m-1`, and symmetry of binomial coefficients.
   At `i = 0` and `i = p^a`, both remainders vanish since `a ≥ n,m`.
4. Write each coefficient as `c * p^(n*r+m*r')`. Its term is
   `c * (x^(p^n))^q * (y^(p^m))^q' * (p^n*x)^r * (p^m*y)^r'`.
   All four bases lie in the subring by hypothesis; closure under powers, products,
   integer multiples, and finite sums proves the power membership. No cancellation
   or division in the ambient ring is needed. -/
theorem exists_prime_pow_add_mem {C : Type u} [CommRing C] (A : Subring C)
    {p : ℕ} (hp : p.Prime) {x y : C} {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hx : x ^ (p ^ n) ∈ A) (hpx : (p : C) ^ n * x ∈ A)
    (hy : y ^ (p ^ m) ∈ A) (hpy : (p : C) ^ m * y ∈ A) :
    ∃ a : ℕ, 0 < a ∧ (x + y) ^ (p ^ a) ∈ A ∧ (p : C) ^ a * (x + y) ∈ A := by
  let a := n * p ^ n + m * p ^ m + n + m
  have han : n ≤ a := by dsimp [a]; omega
  have ham : m ≤ a := by dsimp [a]; omega
  refine ⟨a, by dsimp [a]; omega, ?_, ?_⟩
  · rw [add_pow]
    apply A.sum_mem
    intro i hi
    have hiP : i ≤ p ^ a := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    let j := p ^ a - i
    let r := i % p ^ n
    let s := j % p ^ m
    let D := n * r + m * s
    have hr : r < p ^ n := Nat.mod_lt _ (pow_pos hp.pos _)
    have hs : s < p ^ m := Nat.mod_lt _ (pow_pos hp.pos _)
    have hD : D ≤ n * p ^ n + m * p ^ m :=
      Nat.add_le_add (Nat.mul_le_mul_left n hr.le) (Nat.mul_le_mul_left m hs.le)
    have hdiv : p ^ D ∣ (p ^ a).choose i := by
      by_cases hr0 : r = 0
      · by_cases hs0 : s = 0
        · simp [D, hr0, hs0]
        · have hjP : j ≤ p ^ a := Nat.sub_le _ _
          have hd := pow_dvd_choose_of_mod_ne_zero hp hjP hs0
            (by dsimp [a]; omega : D + m ≤ a)
          simpa only [j, Nat.choose_symm hiP] using hd
      · exact pow_dvd_choose_of_mod_ne_zero hp hiP hr0
          (by dsimp [a]; omega : D + n ≤ a)
    obtain ⟨c, hc⟩ := hdiv
    have hxi : (p : C) ^ (n * r) * x ^ i ∈ A := by
      simpa only [pow_mul] using pow_mod_mul_mem A hx hpx i
    have hyj : (p : C) ^ (m * s) * y ^ j ∈ A := by
      simpa only [pow_mul] using pow_mod_mul_mem A hy hpy j
    have hterm := A.mul_mem (A.mul_mem hxi hyj) (natCast_mem A c)
    have hcast : ((p ^ a).choose i : C) = (p : C) ^ D * (c : C) := by
      rw [hc, Nat.cast_mul, Nat.cast_pow]
    rw [hcast]
    convert hterm using 1
    dsimp [D, j]
    rw [pow_add]
    ring
  · have h₁ := A.mul_mem (natCast_mem A (p ^ (a - n))) hpx
    have h₂ := A.mul_mem (natCast_mem A (p ^ (a - m))) hpy
    have heq : (p : C) ^ a * (x + y) =
        (p ^ (a - n) : ℕ) * ((p : C) ^ n * x) +
          (p ^ (a - m) : ℕ) * ((p : C) ^ m * y) := by
      push_cast
      simp only [← mul_assoc, ← pow_add, Nat.sub_add_cancel han,
        Nat.sub_add_cancel ham, mul_add]
    rw [heq]
    exact A.add_mem h₁ h₂

end Subring
