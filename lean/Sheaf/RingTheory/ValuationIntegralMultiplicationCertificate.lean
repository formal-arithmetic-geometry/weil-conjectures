/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Data.Finset.Max

/-!
# Integral multiplication certificates over a valuation ring

Source: the polynomial-tail argument in steps 4--6 of
`lem-trf-valuation-normalization-localizations`, supplying the background normalization
result used in Temkin, Stable modification of relative curves, Proposition 2.2.1.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ValuationSubring

open Polynomial

/-- Every element has two integral multiplication pairs whose first and last entries
have difference one.

Source: the agent-written polynomial-tail argument in steps 4--6 of
`lem-trf-valuation-normalization-localizations`, used for Temkin, Stable modification
of relative curves, Proposition 2.2.1, converse proof, printed p. 11.
(blueprint: lem-trf-valuation-integral-multiplication-certificate).

Proof: Choose a nonzero polynomial `p` over `K` vanishing at `x`, and a coefficient
`p_k` of maximal valuation among its finite nonzero support. The normalized polynomial
`q = C(p_k^-1) * p` has all coefficients in `V` and `q_k = 1`.
Let `t_n` be the evaluation at `x` of `divX` applied `n` times to `q`. Polynomial
coefficient extraction gives `x*t_(n+1) + q_n = t_n`, with `t_0=0`.
For every valuation subring `T` containing the integral closure, all `t_n` and `x*t_n`
belong to `T`. Induct on `n`: the recurrence first puts `x*t_(n+1)` in `T`.
If `x` belongs to `T`, evaluating the tail polynomial puts `t_(n+1)` in `T` too.
Otherwise `x^-1` belongs to `T` and multiplication gives the same conclusion; at
`x=0`, evaluation is its constant coefficient. The separation form of the valuative
integrality criterion (Stacks Tag 090P, Mathlib
`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`), applied to the normal
integral closure, puts these elements in the integral closure itself.
Take `(a,b,c,d) = (t_k, x*t_k, t_(k+1), x*t_(k+1))`. The recurrence at `k` and
`q_k=1` give `a-d=1`, including the endpoint coefficients and `x=0`. -/
theorem integralClosure_mul_certificate
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (V : ValuationSubring K) (x : L) :
    ∃ a b c d : integralClosure V L,
      (b : L) = x * (a : L) ∧ (d : L) = x * (c : L) ∧ a - d = 1 := by
  classical
  obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) x
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image p.support
    (fun i => V.valuation (p.coeff i)) (Polynomial.support_nonempty.mpr hp0)
  have hk0 : p.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
  let q : K[X] := Polynomial.C (p.coeff k)⁻¹ * p
  have hq : q.eval₂ (algebraMap K L) x = 0 := by
    simp only [q, Polynomial.eval₂_mul, Polynomial.eval₂_C]
    change algebraMap K L (p.coeff k)⁻¹ * (Polynomial.aeval x p) = 0
    rw [hp, mul_zero]
  have hqk : q.coeff k = 1 := by simp [q, Polynomial.coeff_C_mul, hk0]
  have hqV (i : ℕ) : q.coeff i ∈ V := by
    simp only [q, Polynomial.coeff_C_mul]
    by_cases hi : i ∈ p.support
    · obtain ⟨a, ha⟩ := (V.valuation_le_iff (p.coeff i) (p.coeff k)).mp (hmax i hi)
      rw [← ha]
      simp [mul_comm, hk0]
    · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]
      exact V.zero_mem
  let tail : ℕ → K[X] := Nat.rec q (fun _ r => r.divX)
  have tail_zero : tail 0 = q := rfl
  have tail_succ (n : ℕ) : tail (n + 1) = (tail n).divX := rfl
  have tail_coeff (n i : ℕ) : (tail n).coeff i = q.coeff (i + n) := by
    induction n generalizing i with
    | zero => simp only [tail_zero, Nat.add_zero]
    | succ n ih =>
      rw [tail_succ, Polynomial.coeff_divX, ih]
      congr 1
      omega
  let t (n : ℕ) : L := (tail n).eval₂ (algebraMap K L) x
  have t_zero : t 0 = 0 := hq
  have t_rec (n : ℕ) :
      x * t (n + 1) + algebraMap K L ((tail n).coeff 0) = t n := by
    have h := congrArg (fun r : K[X] => r.eval₂ (algebraMap K L) x)
      (Polynomial.X_mul_divX_add (tail n))
    simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
      Polynomial.eval₂_C] using h
  have coeff_mem (n i : ℕ) :
      algebraMap K L ((tail n).coeff i) ∈ integralClosure V L := by
    have hV : (tail n).coeff i ∈ V := by rw [tail_coeff]; exact hqV _
    exact (integralClosure V L).algebraMap_mem ⟨(tail n).coeff i, hV⟩
  have tails_mem (n : ℕ) : t n ∈ integralClosure V L ∧
      x * t n ∈ integralClosure V L := by
    suffices ∀ T : ValuationSubring L,
        (integralClosure V L).toSubring ≤ T.toSubring →
        t n ∈ T ∧ x * t n ∈ T by
      constructor
      · by_contra hn
        obtain ⟨T, hCT, hT⟩ :=
          (integralClosure V L).toSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn
        exact hT (this T hCT).1
      · by_contra hn
        obtain ⟨T, hCT, hT⟩ :=
          (integralClosure V L).toSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn
        exact hT (this T hCT).2
    intro T hCT
    induction n with
    | zero => simp only [t_zero, mul_zero]; exact ⟨T.zero_mem, T.zero_mem⟩
    | succ n ih =>
      have hprod : x * t (n + 1) ∈ T := by
        rw [eq_sub_of_add_eq (t_rec n)]
        exact T.toSubring.sub_mem ih.1 (hCT (coeff_mem n 0))
      refine ⟨?_, hprod⟩
      rcases T.mem_or_inv_mem x with hx | hx
      · change (tail (n + 1)).eval₂ (algebraMap K L) x ∈ T
        rw [Polynomial.eval₂_eq_sum_range]
        exact T.toSubring.sum_mem fun i _ =>
          T.toSubring.mul_mem (hCT (coeff_mem (n + 1) i)) (T.toSubring.pow_mem hx i)
      · by_cases hx0 : x = 0
        · change (tail (n + 1)).eval₂ (algebraMap K L) x ∈ T
          rw [hx0, Polynomial.eval₂_at_zero]
          exact hCT (coeff_mem (n + 1) 0)
        · have hm := T.toSubring.mul_mem hx hprod
          change t (n + 1) ∈ T.toSubring
          simpa only [inv_mul_cancel_left₀ hx0] using hm
  refine ⟨⟨t k, (tails_mem k).1⟩, ⟨x * t k, (tails_mem k).2⟩,
    ⟨t (k + 1), (tails_mem (k + 1)).1⟩,
    ⟨x * t (k + 1), (tails_mem (k + 1)).2⟩, rfl, rfl, ?_⟩
  apply Subtype.ext
  change t k - x * t (k + 1) = 1
  have h := t_rec k
  rw [tail_coeff, Nat.zero_add, hqk, map_one] at h
  exact sub_eq_of_eq_add (by simpa only [add_comm] using h.symm)

end ValuationSubring
