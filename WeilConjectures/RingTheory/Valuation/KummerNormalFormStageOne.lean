/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.KummerNormalForm
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!

# Kummer normal forms, stage 1: terms of value at least `v p`

We continue the setting of `WeilConjectures.RingTheory.Valuation.KummerNormalForm`. Let
`m : Option (ι × ℕ) → Ω` be the lifted Frobenius monomials (`m none = 1`,
`m (some (i, n)) = w i ^ p ^ n`). In stage 1 of the Kummer normal form, a `1`-unit `u ∈ L₁` with
`u ∈ L₂ ^ p`, congruent modulo `{v < v p}` to a combination of the monomials with coefficients in
a *discretely valued* subfield `K* ≤ K`, is multiplied by `p`-th powers of `L₁` until
`v (u - 1) < v p` (`exists_valuation_div_pow_sub_one_lt`).

The leading terms of value `μ ≥ v p` are `p`-th powers of monomials (the residual hypothesis
`hres1`), hence cancelled by dividing by `(1 + c) ^ p` for an explicit `c ∈ L₁`, up to terms of
value `< v p` and products of monomials, which are re-expanded (`hprod`). The value `μ` takes
finitely many values in the discrete value group of `K*`, so the process terminates.

-/

@[expose] public section

open Finset

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation Ω Γ₀} {p : ℕ} {ι : Type*}

/-- The lifted Frobenius monomials: `1` and the `w i ^ p ^ n`. -/
def frobeniusMonomial (p : ℕ) (w : ι → Ω) (j : Option (ι × ℕ)) : Ω :=
  j.elim 1 fun i ↦ w i.1 ^ p ^ i.2

/-- A combination of lifted Frobenius monomials. -/
noncomputable def frobeniusComb (p : ℕ) (w : ι → Ω) (c : Option (ι × ℕ) →₀ Ω) : Ω :=
  c.sum fun j a ↦ a * frobeniusMonomial p w j

variable (p) {w : ι → Ω}

lemma frobeniusComb_add (c c' : Option (ι × ℕ) →₀ Ω) :
    frobeniusComb p w (c + c') = frobeniusComb p w c + frobeniusComb p w c' :=
  Finsupp.sum_add_index' (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul _ _ _

lemma frobeniusComb_single (j : Option (ι × ℕ)) (a : Ω) :
    frobeniusComb p w (Finsupp.single j a) = a * frobeniusMonomial p w j :=
  Finsupp.sum_single_index (zero_mul _)

lemma frobeniusComb_zero : frobeniusComb p w (0 : Option (ι × ℕ) →₀ Ω) = 0 :=
  Finsupp.sum_zero_index

lemma frobeniusComb_smul (a : Ω) (c : Option (ι × ℕ) →₀ Ω) :
    frobeniusComb p w (a • c) = a * frobeniusComb p w c := by
  rw [frobeniusComb, Finsupp.sum_smul_index' (fun _ ↦ zero_mul _), frobeniusComb, Finsupp.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by simp only [smul_eq_mul, mul_assoc]

lemma valuation_frobeniusMonomial (hw1 : ∀ i, v (w i) = 1) (j : Option (ι × ℕ)) :
    v (frobeniusMonomial p w j) = 1 := by
  cases j with
  | none => exact map_one v
  | some i => rw [frobeniusMonomial, Option.elim_some, map_pow, hw1, one_pow]

lemma valuation_frobeniusComb_le (hw1 : ∀ i, v (w i) = 1) (c : Option (ι × ℕ) →₀ Ω) {γ : Γ₀}
    (hc : ∀ j, v (c j) ≤ γ) : v (frobeniusComb p w c) ≤ γ := by
  refine v.map_sum_le fun j _ ↦ ?_
  rw [map_mul, valuation_frobeniusMonomial p hw1, mul_one]
  exact hc j

lemma valuation_frobeniusComb_lt (hw1 : ∀ i, v (w i) = 1) (c : Option (ι × ℕ) →₀ Ω) {γ : Γ₀}
    (hγ : γ ≠ 0) (hc : ∀ j, v (c j) < γ) : v (frobeniusComb p w c) < γ := by
  refine v.map_sum_lt hγ fun j _ ↦ ?_
  rw [map_mul, valuation_frobeniusMonomial p hw1, mul_one]
  exact hc j


/-- A combination of the monomials is `d₀ + ∑ dⱼ (w j.1) ^ p ^ j.2`. -/
lemma frobeniusComb_eq (c : Option (ι × ℕ) →₀ Ω) :
    frobeniusComb p w c = c none + liftedSum p w c.some := by
  rw [frobeniusComb, Finsupp.sum_option_index _ _ (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul _ _ _]
  simp [frobeniusMonomial, liftedSum]

/-- **Stage 1 of the Kummer normal form.** -/
theorem exists_valuation_div_pow_sub_one_lt [DecidableEq ι] (K L₁ L₂ Kst : Subfield Ω)
    (hp : p.Prime) (hp1 : v (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    (hKL₁ : K ≤ L₁) (hL : L₁ ≤ L₂) (hKst : Kst ≤ K)
    (hroot : ∀ c ∈ K, ∃ d ∈ K, d ^ p = c)
    (hw : ∀ i, w i ∈ L₁) (hw1 : ∀ i, v (w i) = 1)
    (hval : ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      ∀ j, v (c j) ≤ v (frobeniusComb p w c))
    (γ : Γ₀) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hdisc : ∀ c ∈ Kst, c ≠ 0 → ∃ n : ℤ, v c = γ ^ n) (N : ℕ) (hN : γ ^ N < v (p : Ω))
    (hprod : ∀ j j', ∃ e : Option (ι × ℕ) →₀ Ω, (∀ k, e k ∈ Kst) ∧
      v (frobeniusMonomial p w j * frobeniusMonomial p w j' - frobeniusComb p w e) < v (p : Ω))
    (hres1 : ∀ z ∈ L₂, v z ≤ 1 → ∀ c : Option (ι × ℕ) →₀ Ω, (∀ j, c j ∈ K) →
      (∀ j, v (c j) ≤ 1) → v (z ^ p - frobeniusComb p w c) < 1 →
        ∀ i : ι, v (c (some (i, 0))) < 1)
    {u : Ω} (hu : u ∈ L₁) (c : Option (ι × ℕ) →₀ Ω) (hc : ∀ j, c j ∈ Kst)
    (hc1 : ∀ j, v (c j) < 1) (hu1 : v (u - 1 - frobeniusComb p w c) < v (p : Ω))
    (h₂ : ∃ y ∈ L₂, y ^ p = u) :
    ∃ g ∈ L₁, g ≠ 0 ∧ v (u / g ^ p - 1) < v (p : Ω) := by
  sorry
