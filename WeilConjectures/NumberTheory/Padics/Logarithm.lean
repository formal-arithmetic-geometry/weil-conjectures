/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.NumberTheory.Padics.Extension

/-!
# The small logarithm of a finite extension of `ℚ_ℓ`

For a finite extension `E/ℚ_ℓ` inside `ℚ̄_ℓ = PadicAlgCl l` the series
`∑ (-1)^(n+1) x ^ n / n` converges for `x` in the maximal ideal of the ring of integers `𝒪_E`,
and on the subgroup `U_E = 1 + ℓ² 𝒪_E` of principal units it is an injective homomorphism to
`(E, +)`.

The topology and the uniform structure of `E` are those restricted from `ℚ̄_ℓ` along the
embedding `E → ℚ̄_ℓ`, i.e. those of `PadicAlgCl.normedFieldOfAlgebra`; they are definitions
rather than instances, since `ℓ` cannot be recovered from `E`. Finiteness of `E` over `ℚ_ℓ` is
what normalises the valuation, `v_ℓ(ℓ) = 1`, and is what makes the series converge on
`ℓ² 𝒪_E` and the logarithm injective there; accordingly every statement of this file assumes
it, while the two definitions, which make sense for any subfield of `ℚ̄_ℓ`, do not.

## Main definitions

- `PadicAlgCl.smallUnits` : the group `U_E = 1 + ℓ² 𝒪_E` of principal units.
- `PadicAlgCl.smallLog` : the logarithm `log (1 + x) = ∑ (-1)^(n+1) x ^ n / n`.

## Main statements

- `PadicAlgCl.summable_logSeries` : the logarithm series converges on `ℓ² 𝒪_E`.
- `PadicAlgCl.smallLog_mul` and `PadicAlgCl.injOn_smallLog` : `u ↦ log u` is an injective
  homomorphism `U_E → (E, +)`.
-/

@[expose] public section

universe w

namespace PadicAlgCl

section Integers

variable {l : ℕ} [Fact l.Prime] {E : Type w} [Field E] [Algebra E (PadicAlgCl l)]

/-- The prime `ℓ` has norm `< 1` in `ℚ̄_ℓ`. -/
theorem nnnorm_natCast_lt_one : ‖(l : PadicAlgCl l)‖₊ < 1 := by
  have h : ‖(l : PadicAlgCl l)‖₊ = 1 / (l : NNReal) := by
    rw [← PadicAlgCl.valuation_def]; exact PadicAlgCl.valuation_p l
  have hl : (0 : NNReal) < (l : NNReal) := by
    exact_mod_cast (Fact.out : l.Prime).pos
  rw [h, div_lt_one hl]
  exact_mod_cast (Fact.out : l.Prime).one_lt

/-- A subfield of `ℚ̄_ℓ` has characteristic zero, so `ℓ ≠ 0` in it. -/
theorem natCast_ne_zero_of_algebra : (l : E) ≠ 0 := by
  intro h
  have h0 : (l : PadicAlgCl l) = 0 := by
    rw [← map_natCast (algebraMap E (PadicAlgCl l)) l, h, map_zero]
  exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h0

/-- The prime `ℓ` lies in the ring of integers `𝒪_E`. -/
theorem natCast_mem_integers : (l : E) ∈ integers l E := by
  rw [mem_integers_iff, map_natCast]
  exact le_of_lt nnnorm_natCast_lt_one

/-- If `a - 1 ∈ ℓ² 𝒪_E`, then `a` is a unit of `𝒪_E`: it is congruent to `1` modulo the
maximal ideal, so its norm is `1`. -/
theorem inv_mem_integers_of_sub_one_div {a : E}
    (ha : (a - 1) / ((l : E) ^ 2) ∈ integers l E) : a⁻¹ ∈ integers l E := by
  have hl0 : (l : E) ≠ 0 := natCast_ne_zero_of_algebra
  set f := algebraMap E (PadicAlgCl l) with hf
  set y := f ((a - 1) / ((l : E) ^ 2)) * (l : PadicAlgCl l) ^ 2 with hy
  have hsmall : ‖y‖₊ < 1 := by
    rw [hy, nnnorm_mul, nnnorm_pow]
    calc ‖f ((a - 1) / ((l : E) ^ 2))‖₊ * ‖(l : PadicAlgCl l)‖₊ ^ 2
        ≤ 1 * ‖(l : PadicAlgCl l)‖₊ ^ 2 := by
          gcongr
          exact (mem_integers_iff l E _).mp ha
      _ = ‖(l : PadicAlgCl l)‖₊ ^ 2 := one_mul _
      _ < 1 := pow_lt_one₀ zero_le nnnorm_natCast_lt_one two_ne_zero
  have hfa : f a = 1 + y := by
    rw [hy, hf, ← map_natCast (algebraMap E (PadicAlgCl l)) l, ← map_pow, ← map_mul,
      ← map_one (algebraMap E (PadicAlgCl l)), ← map_add]
    congr 1
    field_simp
    ring
  have hone : (1 : NNReal) ≤ ‖f a‖₊ := by
    by_cases h : (1 : NNReal) ≤ ‖f a‖₊
    · exact h
    · exfalso
      rw [not_le] at h
      have heq : (1 : PadicAlgCl l) = f a + -y := by rw [hfa]; ring
      have h1 : ‖(1 : PadicAlgCl l)‖ ≤ max ‖f a‖ ‖-y‖ := by
        rw [heq]; exact PadicAlgCl.isNonarchimedean l _ _
      rw [norm_one] at h1
      have hy1 : ‖(-y)‖ < 1 := by rw [norm_neg]; exact_mod_cast hsmall
      have ha1 : ‖f a‖ < 1 := by exact_mod_cast h
      exact absurd h1 (not_le.mpr (max_lt ha1 hy1))
  rw [mem_integers_iff, map_inv₀, nnnorm_inv, inv_le_one₀ (lt_of_lt_of_le zero_lt_one hone)]
  exact hone

/-- The norm of a natural number `m` in `E ⊆ ℚ̄_ℓ` is its `ℓ`-adic norm. -/
theorem norm_algebraMap_natCast (m : ℕ) :
    ‖algebraMap E (PadicAlgCl l) (m : E)‖ = ‖(m : ℚ_[l])‖ := by
  rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]

end Integers

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [instQ : Algebra ℚ_[l] E] [instT : IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [instF : FiniteDimensional ℚ_[l] E]

include instQ instT instF

/-- Blueprint `sk-d-real-log`: Small logarithm.

The subgroup `U_E = 1 + ℓ² 𝒪_E` of `Eˣ`, where `𝒪_E = PadicAlgCl.integers l E` is the ring of
integers of `E`. -/
def smallUnits : Subgroup Eˣ where
  carrier := {u | ((u : E) - 1) / ((l : E) ^ 2) ∈ integers l E}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have hl0 : (l : E) ≠ 0 := natCast_ne_zero_of_algebra
    have key : (((a * b : Eˣ) : E) - 1) / ((l : E) ^ 2)
        = (((a : E) - 1) / ((l : E) ^ 2)) * (((b : E) - 1) / ((l : E) ^ 2)) * ((l : E) ^ 2)
          + ((a : E) - 1) / ((l : E) ^ 2) + ((b : E) - 1) / ((l : E) ^ 2) := by
      push_cast
      field_simp
      ring
    rw [key]
    exact add_mem (add_mem (mul_mem (mul_mem ha hb)
      (pow_mem natCast_mem_integers 2)) ha) hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have hl0 : (l : E) ≠ 0 := natCast_ne_zero_of_algebra
    have ha0 : (a : E) ≠ 0 := a.ne_zero
    have key : (((a⁻¹ : Eˣ) : E) - 1) / ((l : E) ^ 2)
        = -((((a : E) - 1) / ((l : E) ^ 2)) * ((a : E)⁻¹)) := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
      ring
    rw [key]
    exact neg_mem (mul_mem ha (inv_mem_integers_of_sub_one_div ha))

/-- Blueprint `sk-d-real-log`: Small logarithm.

`smallLog l E x` is the sum of the series `log (1 + x) = ∑_{n ≥ 1} (-1)^(n+1) x ^ n / n`,
formed in the topology restricted from `ℚ̄_ℓ`. It converges for `x ∈ ℓ² 𝒪_E`
(`PadicAlgCl.summable_logSeries`), and `u ↦ smallLog l E (u - 1)` is then an injective
homomorphism from `PadicAlgCl.smallUnits` to the additive group of `E`. -/
noncomputable def smallLog (x : E) : E :=
  letI := normedFieldOfAlgebra l E
  ∑' n : ℕ, (-1) ^ n * x ^ (n + 1) / (n + 1 : ℕ)

/-- Blueprint `sk-d-real-log`: Small logarithm.

The logarithm series converges on `ℓ² 𝒪_E`: the `n`-th term has valuation at least
`2 (n + 1) - v_ℓ(n + 1)`, which tends to infinity, and `E` is complete. -/
theorem summable_logSeries {x : E} (hx : x / ((l : E) ^ 2) ∈ integers l E) :
    letI := normedFieldOfAlgebra l E
    Summable fun n : ℕ ↦ (-1) ^ n * x ^ (n + 1) / (n + 1 : ℕ) := by
  sorry

omit instQ instT instF in
/-- Blueprint `sk-d-real-log`: Small logarithm.

On `ℓ² 𝒪_E` the logarithm does not increase the norm, `‖log (1 + x)‖ ≤ ‖x‖`: the term
`x ^ (n + 1) / (n + 1)` has norm `‖x‖ ^ (n + 1) / ‖n + 1‖ ≤ ‖x‖`, as
`‖x‖ ^ n ≤ ‖ℓ‖ ^ (2 n) ≤ ‖ℓ‖ ^ v_ℓ(n + 1) = ‖n + 1‖`, and the norm is nonarchimedean. In
particular `u ↦ log u` is continuous at `1`. -/
theorem norm_smallLog_le {x : E} (hx : x / ((l : E) ^ 2) ∈ integers l E) :
    ‖algebraMap E (PadicAlgCl l) (smallLog l E x)‖ ≤ ‖algebraMap E (PadicAlgCl l) x‖ := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have hnorm (y : E) : ‖y‖ = ‖algebraMap E (PadicAlgCl l) y‖ := rfl
  rw [← hnorm, ← hnorm, smallLog]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n ↦ ?_
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  set r : ℝ := (l : ℝ)⁻¹ with hr
  have hr0 : 0 < r := inv_pos.mpr (zero_lt_one.trans hl)
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ hl.le
  have hlE : ‖(l : E)‖ = r := by
    rw [hnorm, norm_algebraMap_natCast, Padic.norm_p]
  have hxr : ‖x‖ ≤ r ^ 2 := by
    have h := (mem_integers_iff l E _).mp hx
    have h' : ‖x / (l : E) ^ 2‖ ≤ 1 := by
      rw [hnorm]
      exact_mod_cast h
    rwa [norm_div, norm_pow, hlE, div_le_one (pow_pos hr0 2)] at h'
  set v := padicValNat l (n + 1)
  have hv : v ≤ 2 * n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [v]
    · have := (padicValNat_le_nat_log (p := l) (n + 1)).trans (Nat.log_le_self l (n + 1))
      omega
  have hn1 : ‖((n + 1 : ℕ) : E)‖ = r ^ v := by
    rw [hnorm, norm_algebraMap_natCast, Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast
      (Nat.succ_ne_zero n)), Padic.valuation_natCast, hr, inv_pow, zpow_neg, zpow_natCast]
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul, hn1,
    div_le_iff₀ (pow_pos hr0 v), pow_succ']
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg x)
  calc ‖x‖ ^ n ≤ (r ^ 2) ^ n := pow_le_pow_left₀ (norm_nonneg x) hxr n
    _ = r ^ (2 * n) := by rw [← pow_mul]
    _ ≤ r ^ v := pow_le_pow_of_le_one hr0.le hr1 hv

/-- Blueprint `sk-d-real-log`: Small logarithm.

The logarithm turns the multiplication of `U_E` into the addition of `E`. -/
theorem smallLog_mul (u v : smallUnits l E) :
    smallLog l E (((u * v : smallUnits l E) : Eˣ) - 1)
      = smallLog l E (((u : Eˣ) : E) - 1) + smallLog l E (((v : Eˣ) : E) - 1) := by
  sorry

/-- Blueprint `sk-d-real-log`: Small logarithm.

The logarithm is injective on `U_E = 1 + ℓ² 𝒪_E`: on that subgroup the series `exp` converges
and is inverse to `log`. This is what `sk-p-real-rankone` uses to turn a character of `π₁` with
values in `U_E` into a continuous additive character. -/
theorem injOn_smallLog :
    Set.InjOn (fun u : Eˣ ↦ smallLog l E ((u : E) - 1)) (smallUnits l E) := by
  sorry

end PadicAlgCl
