/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Algebra.BigOperators.Intervals
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

namespace Valuation

variable {v}

lemma map_natCast_le_one' (n : ℕ) : v (n : Ω) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact v.map_add_le ih (by rw [map_one])

/-- `(1 + c) ^ p = 1 + c ^ p + p c + B`, `B` the middle binomial terms. -/
lemma one_add_pow_eq (hp : 2 ≤ p) (c : Ω) :
    (1 + c) ^ p = 1 + c ^ p + (p : Ω) * c +
      ∑ i ∈ Ico 2 p, (p.choose i : Ω) * c ^ i := by
  rw [add_comm (1 : Ω) c, add_pow]
  simp only [one_pow, mul_one]
  have h1 : range (p + 1) = insert p (insert 0 (insert 1 (Ico 2 p))) := by
    ext i; simp only [mem_range, mem_insert, mem_Ico]; omega
  rw [h1, sum_insert (by simp <;> omega), sum_insert (by simp <;> omega),
    sum_insert (by simp <;> omega)]
  simp only [Nat.choose_self, Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one,
    Nat.cast_one, mul_one]
  rw [sum_congr rfl fun i _ ↦ mul_comm (c ^ i) _]
  ring

/-- The middle binomial terms of `(1 + c) ^ p` are negligible when `v c ^ p < v p`. -/
lemma isKummerNegligible_binomial (hp : p.Prime) (hp1 : v (p : Ω) < 1) {c : Ω}
    (hc : v c ^ p < v (p : Ω)) :
    v.IsKummerNegligible p (∑ i ∈ Ico 2 p, (p.choose i : Ω) * c ^ i) := by
  have hp2 := hp.two_le
  have hc1 : v c < 1 := by
    by_contra h
    rw [not_lt] at h
    exact (not_le.2 (hc.trans hp1)) (one_le_pow₀ h)
  -- each term has value `≤ v p * v c ^ 2`, which is negligible
  have hneg : ∀ x : Ω, v x ≤ v (p : Ω) * v c ^ 2 → v.IsKummerNegligible p x := by
    intro x hx
    refine (pow_le_pow_left₀ zero_le hx _).trans ?_
    rw [mul_pow, ← pow_mul]
    calc v (p : Ω) ^ (p - 1) * v c ^ (2 * (p - 1))
        ≤ v (p : Ω) ^ (p - 1) * v c ^ p :=
          mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' hc1.le (by omega))
      _ ≤ v (p : Ω) ^ (p - 1) * v (p : Ω) := mul_le_mul' le_rfl hc.le
      _ = v (p : Ω) ^ p := by rw [← pow_succ]; congr 1; omega
  refine hneg _ (v.map_sum_le fun i hi ↦ ?_)
  rw [mem_Ico] at hi
  obtain ⟨m, hm⟩ := hp.dvd_choose_self (by omega : i ≠ 0) hi.2
  rw [hm, Nat.cast_mul, map_mul, map_mul, map_pow]
  calc v (p : Ω) * v (m : Ω) * v c ^ i ≤ v (p : Ω) * 1 * v c ^ 2 :=
        mul_le_mul' (mul_le_mul' le_rfl (map_natCast_le_one' m))
          (pow_le_pow_right_of_le_one' hc1.le hi.1)
    _ = v (p : Ω) * v c ^ 2 := by rw [mul_one]

end Valuation

section Stage2

/-- The combination `∑ⱼ dⱼ (w j.1) ^ p ^ j.2` of lifted Frobenius powers. -/
noncomputable def liftedSum (p : ℕ) {ι : Type*} (w : ι → Ω) (d : ι × ℕ →₀ Ω) : Ω :=
  d.sum fun j c ↦ c * w j.1 ^ p ^ j.2

variable {v p} {ι : Type*} (w : ι → Ω)

variable {w} in
lemma liftedSum_add (d d' : ι × ℕ →₀ Ω) :
    liftedSum p w (d + d') = liftedSum p w d + liftedSum p w d' :=
  Finsupp.sum_add_index' (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul _ _ _

lemma liftedSum_single (j : ι × ℕ) (c : Ω) :
    liftedSum p w (Finsupp.single j c) = c * w j.1 ^ p ^ j.2 :=
  Finsupp.sum_single_index (zero_mul _)

lemma liftedSum_erase [DecidableEq ι] (d : ι × ℕ →₀ Ω) (j : ι × ℕ) :
    liftedSum p w d = liftedSum p w (d.erase j) + d j * w j.1 ^ p ^ j.2 := by
  conv_lhs => rw [← Finsupp.erase_add_single j d]
  rw [liftedSum_add, liftedSum_single]

/-- The value of a lifted sum is at most the largest value of its coefficients. -/
lemma valuation_liftedSum_le (hw1 : ∀ i, v (w i) = 1) (d : ι × ℕ →₀ Ω) {γ : Γ₀}
    (hd : ∀ j, v (d j) ≤ γ) : v (liftedSum p w d) ≤ γ := by
  refine v.map_sum_le fun j _ ↦ ?_
  rw [map_mul, map_pow, hw1, one_pow, mul_one]
  exact hd j

end Stage2

section Stage2Step

variable {v p} {ι : Type*} {w : ι → Ω}

lemma valuation_one_add_eq_one {x : Ω} (hx : v x < 1) : v (1 + x) = 1 := by
  rw [add_comm, Valuation.map_add_eq_of_lt_right v (by rwa [map_one])]
  exact map_one v

/-- **One replacement step of stage 2**: a term `d (w i) ^ p ^ (k + 1)` of value `< v p` is
replaced, up to the `p`-th power `(1 + c) ^ p` (`c = d^{1/p} (w i) ^ p ^ k`) and a negligible
error, by `- p d^{1/p} (w i) ^ p ^ k`. -/
lemma kummer_stage2_step [DecidableEq ι] (hp : p.Prime) (hp1 : v (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    (hw1 : ∀ i, v (w i) = 1) (d : ι × ℕ →₀ Ω) (hdv : ∀ j, v (d j) < v (p : Ω)) {d₀ : Ω}
    (hd₀ : v d₀ < v (p : Ω)) {n : Ω} (hn : v.IsKummerNegligible p n) (i : ι) (k : ℕ) {e : Ω}
    (he : e ^ p = d (i, k + 1)) :
    ∃ n', v.IsKummerNegligible p n' ∧
      (1 + d₀ + liftedSum p w d) * (1 + n) = (1 + e * w i ^ p ^ k) ^ p *
        ((1 + d₀ + liftedSum p w (d.erase (i, k + 1) + Finsupp.single (i, k) (-(p : Ω) * e))) *
          (1 + n')) ∧
      v (e * w i ^ p ^ k) < 1 ∧
      ∀ j, v ((d.erase (i, k + 1) + Finsupp.single (i, k) (-(p : Ω) * e)) j) < v (p : Ω) := by
  have hp2 := hp.two_le
  set c := e * w i ^ p ^ k with hcdef
  set d' := d.erase (i, k + 1) + Finsupp.single (i, k) (-(p : Ω) * e) with hd'def
  set T := d₀ + liftedSum p w d' with hTdef
  have hvp : 0 < v (p : Ω) := v.pos_iff.2 hp0
  have hvce : v c = v e := by rw [hcdef, map_mul, map_pow, hw1, one_pow, mul_one]
  have hvc : v c ^ p = v (d (i, k + 1)) := by rw [hvce, ← map_pow, he]
  have hvcp : v c ^ p < v (p : Ω) := hvc ▸ hdv _
  have hc1 : v c < 1 := by
    by_contra h
    rw [not_lt] at h
    exact (not_le.2 (hvcp.trans hp1)) (one_le_pow₀ h)
  have he1 : v e < 1 := hvce ▸ hc1
  have hd' : ∀ j, v (d' j) < v (p : Ω) := by
    intro j
    rw [hd'def, Finsupp.add_apply]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
    · rw [Finsupp.erase_apply]
      split_ifs
      · rw [map_zero]; exact hvp
      · exact hdv j
    · rw [Finsupp.single_apply]
      split_ifs
      · rw [map_mul, v.map_neg]
        exact mul_lt_of_lt_one_right hvp he1
      · rw [map_zero]; exact hvp
  have hSd : liftedSum p w d = liftedSum p w d' + c ^ p + (p : Ω) * c := by
    rw [liftedSum_erase w d (i, k + 1), hd'def, liftedSum_add, liftedSum_single, hcdef,
      mul_pow, ← pow_mul, ← pow_succ, he]
    ring
  have hTv : v T < v (p : Ω) := by
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt hd₀ ?_)
    exact v.map_sum_lt hvp.ne' fun j _ ↦ by
      rw [map_mul, map_pow, hw1, one_pow, mul_one]; exact hd' j
  have hT1 : v T < 1 := hTv.trans hp1
  have hB := Valuation.isKummerNegligible_binomial p hp hp1 hvcp
  set B := ∑ i ∈ Ico 2 p, (p.choose i : Ω) * c ^ i with hBdef
  set D := (1 + c) ^ p * (1 + T) with hDdef
  have hD : v D = 1 := by
    rw [hDdef, map_mul, map_pow, valuation_one_add_eq_one hc1, valuation_one_add_eq_one hT1,
      one_pow, one_mul]
  have hD0 : D ≠ 0 := by intro h; rw [h, map_zero] at hD; exact zero_ne_one hD
  set A := 1 + d₀ + liftedSum p w d with hAdef
  have hA1 : v A ≤ 1 := by
    rw [hAdef, hSd]
    refine v.map_add_le (v.map_add_le (by rw [map_one]) (hd₀.trans hp1).le)
      (v.map_add_le (v.map_add_le ?_ ?_) ?_)
    · exact v.map_sum_le fun j _ ↦ by
        rw [map_mul, map_pow, hw1, one_pow, mul_one]; exact (hd' j).le.trans hp1.le
    · rw [map_pow]; exact pow_le_one' hc1.le _
    · rw [map_mul]; exact mul_le_one' hp1.le hc1.le
  have hkey : A * (1 + n) - D = A * n - T * (c ^ p + (p : Ω) * c) - B * (1 + T) := by
    rw [hDdef, Valuation.one_add_pow_eq p hp.two_le c, hAdef, hSd, hTdef]
    ring
  have hnum : v.IsKummerNegligible p (A * (1 + n) - D) := by
    rw [hkey]
    have hAn : v.IsKummerNegligible p (A * n) := by rw [mul_comm]; exact hn.mul_of_le_one hA1
    refine (hAn.sub ?_).sub ?_
    · refine Valuation.IsKummerNegligible.mul_of_lt hp.two_le hp1 hTv ?_
      refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
      · rw [map_pow]; exact hvcp
      · rw [map_mul]; exact mul_lt_of_lt_one_right hvp hc1
    · exact hB.mul_of_le_one (v.map_add_le (by rw [map_one]) hT1.le)
  refine ⟨(A * (1 + n) - D) / D, ?_, ?_, hc1, hd'⟩
  · refine hnum.of_le ?_
    rw [map_div₀, hD, div_one]
  · have hD' : (1 + c) ^ p * (1 + d₀ + liftedSum p w d') = D := by
      rw [hDdef, hTdef, add_assoc]
    rw [← mul_assoc, hD']
    field_simp
    ring

end Stage2Step
