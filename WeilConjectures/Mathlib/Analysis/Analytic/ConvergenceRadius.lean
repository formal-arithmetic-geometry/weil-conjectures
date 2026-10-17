/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# The radius of convergence of a formal power series

A formal power series `f = ∑ aₙ Tⁿ ∈ 𝕜⟦X⟧` over a nontrivially normed field has a radius of
convergence `R(f) ∈ ℝ≥0∞`, the supremum of all `r ≥ 0` such that `∑ₙ ‖aₙ‖ tⁿ` converges for
every `0 ≤ t < r`.

Rather than redoing the classical theory we reduce to Mathlib's radius of convergence of a
formal multilinear series: the scalar series `∑ aₙ Tⁿ` is `FormalMultilinearSeries.ofScalars`
applied to the coefficients of `f`, and `FormalMultilinearSeries.radius` of that series is the
usual radius of convergence.

This file also introduces nonnegative series, those all of whose complex coefficients lie in
`ℝ≥0`, and proves the comparison results of the real-sheaves chapter: a factor of a convergent
product of nonnegative series with constant term `1` has at least the radius of the product
(`lem-rp-positive-product-radius`), and a polynomial whose inverse has radius `R` has no zero in
the open disc of radius `R`.

## Main definitions

- `PowerSeries.radius` : the radius of convergence `R(f) ∈ ℝ≥0∞` of `f : 𝕜⟦X⟧`.
- `PowerSeries.HasNonnegCoeffs` : all coefficients of `f : ℂ⟦X⟧` are nonnegative reals.

## Main statements

- `PowerSeries.radius_le_radius_of_norm_coeff_le` : coefficientwise domination bounds radii.
- `PowerSeries.min_radius_le_radius_mul` : the radius of a product is at least the smaller radius.
- `PowerSeries.le_radius_coe_mul_inv_prod` : a polynomial divided by `∏ (1 - c X)` converges on
  every disc on which all the `1 - c X` are invertible.
- `PowerSeries.eval_ne_zero_of_lt_radius_inv` : a polynomial has no zero inside the disc of
  convergence of its inverse.
- `PowerSeries.radius_tprod_le_radius` : a factor of a convergent product of nonnegative series
  with constant term `1` has at least the radius of the product.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace PowerSeries

/-- Blueprint `sk-d-real-series`, `d-real-series`: Radius of a formal series.

The radius of convergence `R(f) ∈ ℝ≥0∞` of a formal power series `f = ∑ aₙ Tⁿ ∈ 𝕜⟦X⟧` over a
nontrivially normed field `𝕜`.

This is defined as the radius of convergence of the associated formal multilinear series
`FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ coeff n f)`, whose `n`-th coefficient is `aₙ` by
`FormalMultilinearSeries.coeff_ofScalars`. It agrees with the description in the blueprint as
the supremum of the `r ≥ 0` for which `∑ₙ ‖aₙ‖ tⁿ` converges for all `0 ≤ t < r`: by
`FormalMultilinearSeries.radius` it is the supremum of the `r ≥ 0` for which `‖aₙ‖ rⁿ` is
bounded, and boundedness of `‖aₙ‖ rⁿ` for one `r` is equivalent to summability of
`∑ₙ ‖aₙ‖ tⁿ` for all `t < r` (`FormalMultilinearSeries.summable_norm_mul_pow` and
`FormalMultilinearSeries.le_radius_of_summable_norm`). -/
noncomputable def radius {𝕜 : Type*} [NontriviallyNormedField 𝕜] (f : 𝕜⟦X⟧) : ℝ≥0∞ :=
  (FormalMultilinearSeries.ofScalars 𝕜 fun n ↦ coeff n f).radius

/-- Blueprint `sk-d-real-series`, `d-real-series`: Radius of a formal series.

A formal power series `f = ∑ aₙ Tⁿ ∈ ℂ⟦X⟧` has nonnegative coefficients if every `aₙ` is a
nonnegative real number. These are the series for which the coefficientwise comparison
arguments of the real-sheaves chapter apply: a coefficientwise bound between them is preserved
by products and gives a bound on the radius of convergence. -/
def HasNonnegCoeffs (f : ℂ⟦X⟧) : Prop :=
  ∀ n, coeff n f ∈ Set.range ((↑) : ℝ≥0 → ℂ)

section Radius

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Inside the radius of convergence the series of norms `∑ ‖aₙ‖ rⁿ` converges. -/
theorem summable_norm_coeff_mul_pow {f : 𝕜⟦X⟧} {r : ℝ≥0} (h : (r : ℝ≥0∞) < f.radius) :
    Summable fun n ↦ ‖coeff n f‖ * (r : ℝ) ^ n := by
  simpa [FormalMultilinearSeries.ofScalars_norm] using
    (FormalMultilinearSeries.ofScalars 𝕜 fun n ↦ coeff n f).summable_norm_mul_pow h

/-- If the series of norms `∑ ‖aₙ‖ rⁿ` converges, then `r` is at most the radius. -/
theorem le_radius_of_summable {f : 𝕜⟦X⟧} {r : ℝ≥0}
    (h : Summable fun n ↦ ‖coeff n f‖ * (r : ℝ) ^ n) : (r : ℝ≥0∞) ≤ f.radius :=
  (FormalMultilinearSeries.ofScalars 𝕜 fun n ↦ coeff n f).le_radius_of_summable_norm
    (by simpa [FormalMultilinearSeries.ofScalars_norm] using h)

/-- If `‖aₙ‖ rⁿ` is bounded, then `r` is at most the radius. -/
theorem le_radius_of_bound {f : 𝕜⟦X⟧} {r : ℝ≥0} (B : ℝ)
    (h : ∀ n, ‖coeff n f‖ * (r : ℝ) ^ n ≤ B) : (r : ℝ≥0∞) ≤ f.radius :=
  (FormalMultilinearSeries.ofScalars 𝕜 fun n ↦ coeff n f).le_radius_of_bound B
    (by simpa [FormalMultilinearSeries.ofScalars_norm] using h)

/-- A series whose coefficients are dominated in norm by those of `g` has at least the radius
of `g`. -/
theorem radius_le_radius_of_norm_coeff_le {f g : 𝕜⟦X⟧} (h : ∀ n, ‖coeff n f‖ ≤ ‖coeff n g‖) :
    g.radius ≤ f.radius :=
  ENNReal.le_of_forall_nnreal_lt fun _ hr ↦ le_radius_of_summable <|
    (summable_norm_coeff_mul_pow hr).of_nonneg_of_le (fun _ ↦ by positivity)
      fun n ↦ mul_le_mul_of_nonneg_right (h n) (by positivity)

/-- The radius of a product of two series is at least the smaller of their radii: inside both
discs the Cauchy product of the two absolutely convergent series converges absolutely. -/
theorem min_radius_le_radius_mul (f g : 𝕜⟦X⟧) : min f.radius g.radius ≤ (f * g).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ le_radius_of_summable ?_
  set a : ℕ → ℝ := fun n ↦ ‖coeff n f‖ * (r : ℝ) ^ n
  set b : ℕ → ℝ := fun n ↦ ‖coeff n g‖ * (r : ℝ) ^ n
  have ha : Summable fun n ↦ ‖a n‖ := by
    simpa [a, abs_of_nonneg] using summable_norm_coeff_mul_pow (hr.trans_le (min_le_left _ _))
  have hb : Summable fun n ↦ ‖b n‖ := by
    simpa [b, abs_of_nonneg] using summable_norm_coeff_mul_pow (hr.trans_le (min_le_right _ _))
  refine (summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb).of_nonneg_of_le
    (fun _ ↦ by positivity) fun n ↦ ?_
  rw [coeff_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity)]
  calc ‖∑ p ∈ Finset.antidiagonal n, coeff p.1 f * coeff p.2 g‖ * (r : ℝ) ^ n
      ≤ (∑ p ∈ Finset.antidiagonal n, ‖coeff p.1 f‖ * ‖coeff p.2 g‖) * (r : ℝ) ^ n := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_mul_le _ _)
    _ = ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [← Finset.mem_antidiagonal.1 hp, pow_add]
        ring

/-- A polynomial has infinite radius of convergence. -/
theorem radius_coe (P : Polynomial 𝕜) : (P : 𝕜⟦X⟧).radius = ⊤ :=
  ENNReal.eq_top_of_forall_nnreal_le fun _ ↦ le_radius_of_summable <|
    summable_of_ne_finset_zero (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt
        (by simpa [Nat.lt_succ_iff] using hn), norm_zero, zero_mul]

/-- The inverse of `1 - c X` is the geometric series `∑ cⁿ Xⁿ`. -/
theorem inv_one_sub_C_mul_X (c : 𝕜) : (1 - C c * X : 𝕜⟦X⟧)⁻¹ = mk (c ^ ·) := by
  refine ((PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2 ?_).symm
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_mul_X, mul_comm, coeff_C_mul, coeff_mk, coeff_mk, pow_succ']
    simp

/-- The geometric series `(1 - c X)⁻¹` converges on the disc of radius `r` when `‖c‖ r < 1`. -/
theorem le_radius_inv_one_sub_C_mul_X {c : 𝕜} {r : ℝ≥0} (hr : ‖c‖ * r < 1) :
    (r : ℝ≥0∞) ≤ (1 - C c * X : 𝕜⟦X⟧)⁻¹.radius := by
  refine le_radius_of_summable ?_
  simp only [inv_one_sub_C_mul_X, coeff_mk, norm_pow, ← mul_pow]
  exact summable_geometric_of_lt_one (by positivity) hr

/-- A polynomial divided by `∏ (1 - c X)` converges on the disc of radius `r` as soon as
`‖c‖ r < 1` for all `c`. -/
theorem le_radius_coe_mul_inv_prod (P : Polynomial 𝕜) (s : Multiset 𝕜) {r : ℝ≥0}
    (hr : ∀ c ∈ s, ‖c‖ * r < 1) :
    (r : ℝ≥0∞) ≤ ((P : 𝕜⟦X⟧) * ((s.map fun c ↦ 1 - C c * X).prod)⁻¹).radius := by
  induction s using Multiset.induction_on generalizing P with
  | empty => simp [radius_coe]
  | cons c s ih =>
    have h : (P : 𝕜⟦X⟧) * ((((c ::ₘ s).map fun c ↦ 1 - C c * X).prod)⁻¹) =
        (1 - C c * X)⁻¹ * ((P : 𝕜⟦X⟧) * ((s.map fun c ↦ 1 - C c * X).prod)⁻¹) := by
      rw [Multiset.map_cons, Multiset.prod_cons, MvPowerSeries.mul_inv_rev]
      ring
    rw [h]
    refine le_trans (le_min ?_ (ih P fun c hc ↦ hr c (Multiset.mem_cons_of_mem hc)))
      (min_radius_le_radius_mul _ _)
    exact le_radius_inv_one_sub_C_mul_X (hr c (Multiset.mem_cons_self c s))

/-- A polynomial with nonzero constant term has no zero inside the disc of convergence of its
inverse: at such a zero `z` the Cauchy product of the convergent series `P (z) = ∑ pₙ zⁿ` and
`P⁻¹ (z) = ∑ bₙ zⁿ` would be the value `1` of the series `P P⁻¹ = 1`. -/
theorem eval_ne_zero_of_lt_radius_inv [CompleteSpace 𝕜] {P : Polynomial 𝕜} (hP : P.coeff 0 ≠ 0)
    {z : 𝕜} (hz : (‖z‖₊ : ℝ≥0∞) < ((P : 𝕜⟦X⟧)⁻¹).radius) : P.eval z ≠ 0 := by
  set G := (P : 𝕜⟦X⟧)⁻¹
  have hPG : (P : 𝕜⟦X⟧) * G = 1 :=
    PowerSeries.mul_inv_cancel _ (by rwa [← coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe])
  have hf : Summable fun n ↦ ‖P.coeff n * z ^ n‖ :=
    summable_of_ne_finset_zero (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hn),
        zero_mul, norm_zero]
  have hg : Summable fun n ↦ ‖coeff n G * z ^ n‖ := by
    simpa [norm_mul, norm_pow] using summable_norm_coeff_mul_pow hz
  have key := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  have hP : ∑' n, P.coeff n * z ^ n = P.eval z := by
    rw [tsum_eq_sum (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hn),
        zero_mul], Polynomial.eval_eq_sum_range]
  have h1 : ∑' n, ∑ p ∈ Finset.antidiagonal n, P.coeff p.1 * z ^ p.1 * (coeff p.2 G * z ^ p.2)
      = 1 := by
    have h (n : ℕ) : ∑ p ∈ Finset.antidiagonal n, P.coeff p.1 * z ^ p.1 * (coeff p.2 G * z ^ p.2)
        = coeff n ((P : 𝕜⟦X⟧) * G) * z ^ n := by
      rw [coeff_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [← Finset.mem_antidiagonal.1 hp, pow_add, Polynomial.coeff_coe]
      ring
    simp_rw [h, hPG, coeff_one]
    rw [tsum_eq_single 0 fun n hn ↦ by simp [hn]]
    simp
  rw [hP, h1] at key
  exact left_ne_zero_of_mul_eq_one key

end Radius

section Nonneg

open scoped ComplexOrder PowerSeries.WithPiTopology

theorem hasNonnegCoeffs_iff {f : ℂ⟦X⟧} : f.HasNonnegCoeffs ↔ ∀ n, 0 ≤ coeff n f := by
  refine forall_congr' fun n ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨a, ha⟩
    rw [← ha]
    exact Complex.zero_le_real.2 a.2
  · obtain ⟨a, ha, h⟩ := RCLike.nonneg_iff_exists_ofReal.1 h
    exact ⟨⟨a, ha⟩, h⟩

/-- Blueprint `lem-rp-positive-product-radius`: Positive products and radii of convergence.

Let `(f_j)` be a family of series in `1 + T ℝ≥0⟦T⟧` whose product converges in the product
topology. Then every factor `f_j` has radius of convergence at least that of the product.

Indeed nonnegativity and the constant terms `1` give the coefficientwise inequality
`0 ≤ a_{j, n} ≤ A_n` between the coefficients of `f_j` and those of the product, first for the
finite partial products containing `f_j` and then, the set of such series being closed, for the
product itself. -/
theorem radius_tprod_le_radius {J : Type*} {f : J → ℂ⟦X⟧} (hf : ∀ j, (f j).HasNonnegCoeffs)
    (h1 : ∀ j, constantCoeff (f j) = 1) (hmul : Multipliable f) (j : J) :
    (∏' i, f i).radius ≤ (f j).radius := by
  classical
  simp_rw [hasNonnegCoeffs_iff] at hf
  -- the series with nonnegative coefficients dominating `f j`
  let D : Set ℂ⟦X⟧ := {g | ∀ n, coeff n (f j) ≤ coeff n g}
  have hD : IsClosed D := by
    have : D = ⋂ n, {g | coeff n (f j) ≤ coeff n g} := by ext; simp [D]
    rw [this]
    exact isClosed_iInter fun n ↦ isClosed_le continuous_const
      (WithPiTopology.continuous_coeff ℂ n)
  have hmono (g h : ℂ⟦X⟧) (hg : ∀ n, 0 ≤ coeff n g) (hh : ∀ n, 0 ≤ coeff n h)
      (hh1 : constantCoeff h = 1) : ∀ n, coeff n g ≤ coeff n (g * h) := by
    intro n
    rw [coeff_mul, ← Finset.add_sum_erase _ _
      (show ((n, 0) : ℕ × ℕ) ∈ Finset.antidiagonal n by simp)]
    simp only [coeff_zero_eq_constantCoeff_apply, hh1, mul_one, le_add_iff_nonneg_right]
    exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hg _) (hh _)
  have hnonneg (s : Finset J) : ∀ n, 0 ≤ coeff n (∏ i ∈ s, f i) := by
    induction s using Finset.induction_on with
    | empty => intro n; rw [Finset.prod_empty, coeff_one]; split_ifs <;> simp
    | insert a s ha ih =>
      intro n
      rw [Finset.prod_insert ha, coeff_mul]
      exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hf a _) (ih _)
  have hconst (s : Finset J) : constantCoeff (∏ i ∈ s, f i) = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun i _ ↦ h1 i
  have hev : ∀ᶠ s in Filter.atTop, ∏ i ∈ s, f i ∈ D := by
    filter_upwards [Filter.eventually_ge_atTop {j}] with s hs
    rw [← Finset.mul_prod_erase s f (Finset.singleton_subset_iff.1 hs)]
    exact hmono _ _ (hf j) (hnonneg _) (hconst _)
  have hmem : ∏' i, f i ∈ D := hD.mem_of_tendsto hmul.hasProd hev
  refine radius_le_radius_of_norm_coeff_le fun n ↦ ?_
  obtain ⟨a, ha, hfa⟩ := RCLike.nonneg_iff_exists_ofReal.1 (hf j n)
  obtain ⟨b, hb, hfb⟩ := RCLike.nonneg_iff_exists_ofReal.1 ((hf j n).trans (hmem n))
  have hab := hmem n
  rw [← hfa, ← hfb] at hab ⊢
  rw [RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg ha, abs_of_nonneg hb]
  exact_mod_cast hab

end Nonneg

end PowerSeries
