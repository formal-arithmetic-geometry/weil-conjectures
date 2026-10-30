/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!

# Kummer normal forms over a Frobenius-closed lifted basis (mixed characteristic)

Let `Ω` be a field with a valuation `v` and `p` a prime with `0 < v p < 1` (mixed
characteristic), `K ≤ L₁ ≤ L₂` subfields with `K` closed under `p`-th roots, and `w : ι → L₁` a
family of units which is valuation independent over `K`. We show that a `1`-unit `u ∈ L₁ ∩ L₂^p`
is a `p`-th power in `L₁` (`exists_pow_eq_of_approx`), given approximations of the elements of
`L₁` by `K`-combinations of the `w i ^ p ^ n` and the usual residual hypothesis `hres` on `L₂`.

The proof follows F.-V. Kuhlmann, *Elimination of ramification I*, Trans. AMS 362 (2010),
Prop. 4.16, in two stages, where an element `x` is *negligible* if `v x ^ (p - 1) ≤ v p ^ p`
(i.e. its additive value is at least `p v(p)/(p-1)`), so that `1 + x` is a `p`-th power by
Hensel's lemma:
* stage 1, for terms of value `≥ v p`: modulo `1 + p𝔪`, `(1 + c) ^ p ≡ 1 + c ^ p`; the leading
  terms are `p`-th powers of lifted basis elements, which are cancelled exactly; the values of
  the terms stay in a finitely generated monoid, so the process terminates;
* stage 2, for terms of value `< v p`: modulo negligible elements the problem is linear, and a
  term `d w ^ p ^ (n + 1)` is replaced by `- p d^{1/p} w ^ p ^ n`.

-/

@[expose] public section

open Finset

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation Ω Γ₀) (p : ℕ)

/-- An element is *negligible* (for the Kummer theory of exponent `p`) if its additive value is
at least `p v(p) / (p - 1)`. -/
def Valuation.IsKummerNegligible (x : Ω) : Prop :=
  v x ^ (p - 1) ≤ v (p : Ω) ^ p

namespace Valuation.IsKummerNegligible

variable {v p}

lemma zero (hp : 1 < p) : v.IsKummerNegligible p 0 := by
  rw [IsKummerNegligible, map_zero, zero_pow (by omega)]
  exact zero_le

lemma add {x y : Ω} (hx : v.IsKummerNegligible p x) (hy : v.IsKummerNegligible p y) :
    v.IsKummerNegligible p (x + y) := by
  rcases le_total (v x) (v y) with h | h
  · exact (pow_le_pow_left₀ zero_le ((v.map_add x y).trans (max_eq_right h).le) _).trans hy
  · exact (pow_le_pow_left₀ zero_le ((v.map_add x y).trans (max_eq_left h).le) _).trans hx

lemma neg {x : Ω} (hx : v.IsKummerNegligible p x) : v.IsKummerNegligible p (-x) := by
  rwa [IsKummerNegligible, map_neg]

lemma sub {x y : Ω} (hx : v.IsKummerNegligible p x) (hy : v.IsKummerNegligible p y) :
    v.IsKummerNegligible p (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

lemma mul_of_le_one {x y : Ω} (hx : v.IsKummerNegligible p x) (hy : v y ≤ 1) :
    v.IsKummerNegligible p (x * y) := by
  refine le_trans ?_ hx
  rw [map_mul, mul_pow]
  exact mul_le_of_le_one_right' (pow_le_one' hy _)

lemma of_le {x y : Ω} (hx : v.IsKummerNegligible p x) (h : v y ≤ v x) :
    v.IsKummerNegligible p y :=
  (pow_le_pow_left₀ zero_le h _).trans hx

/-- The product of two elements of value `< v p` is negligible. -/
lemma mul_of_lt (hp : 2 ≤ p) (hp1 : v (p : Ω) < 1) {x y : Ω} (hx : v x < v (p : Ω))
    (hy : v y < v (p : Ω)) : v.IsKummerNegligible p (x * y) := by
  rw [IsKummerNegligible, map_mul, mul_pow]
  calc v x ^ (p - 1) * v y ^ (p - 1) ≤ v (p : Ω) ^ (p - 1) * v (p : Ω) ^ (p - 1) :=
        mul_le_mul' (pow_le_pow_left₀ zero_le hx.le _) (pow_le_pow_left₀ zero_le hy.le _)
    _ = v (p : Ω) ^ (2 * (p - 1)) := by rw [← pow_add]; ring_nf
    _ ≤ v (p : Ω) ^ p := pow_le_pow_right_of_le_one' hp1.le (by omega)

end Valuation.IsKummerNegligible
