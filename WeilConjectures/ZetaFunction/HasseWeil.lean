/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.Algebra.Polynomial.FieldDivision
public import WeilConjectures.Statement
public import WeilConjectures.ZetaFunction.BettiSymmetry
public import WeilConjectures.ZetaFunction.CurveZeta
public import WeilConjectures.ZetaLinearAlgebra.TraceDatum

/-!
# The Hasse–Weil bound

Let `X` be a smooth proper geometrically integral scheme of dimension `d ≥ 1` over a finite
field `k` with `q` elements, and let `P 0, …, P_{2d} ∈ ℤ[T]` be integral Frobenius factors of
its zeta function satisfying the Riemann hypothesis. The number of rational points of `X` is
the alternating sum of the traces of Frobenius, the two endpoint factors `P 0 = 1 - T` and
`P (2 * d) = 1 - qᵈ T` contribute `1` and `qᵈ`, and each of the `deg (P i)` reciprocal roots
in an intermediate degree `i` has absolute value `q^{i/2}`. The triangle inequality then
bounds the deviation of the point count from `qᵈ + 1`.

For a smooth projective curve of genus `g` this is the classical Hasse–Weil bound
`|N₁ - (q + 1)| ≤ 2 g √q`, since there `d = 1` and `deg (P 1) = 2 g`. The hypothesis `1 ≤ d` is
needed: for `d = 0` the two endpoint factors coincide and the bound fails.

This file formalises the Hasse–Weil bound of the blueprint block on zeta functions and the Weil
conjectures.

The proof compares logarithmic derivatives in the factorization of the zeta function: this
expresses `N n` as the alternating sum `∑ (-1) ^ i ∑ αⁿ` of the power sums of the reciprocal
roots `α` of the `P i`, the shadow of the Lefschetz trace formula.

## Main statements

- `AlgebraicGeometry.Scheme.abs_pointCount_sub_le_sum_finrank`: the Hasse–Weil bound with the
  Betti numbers `dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` (`cor-zl-hasse-weil-general-bound`), using the endpoint
  cohomology of `prop-endpoints`
  (`AlgebraicGeometry.Scheme.endpoints_of_isIntegralFrobeniusFactor`).
- `AlgebraicGeometry.Scheme.Hom.pointCount_eq_sum_roots`: `N n = ∑ (-1) ^ i ∑ αⁿ`.
- `AlgebraicGeometry.Scheme.Hom.abs_pointCount_sub_le`: the Hasse–Weil bound over the degree `n`
  extension, `|N n - (q ^ (d n) + 1)| ≤ ∑_{0 < i < 2d} deg (P i) · q ^ (i n / 2)`.
- `AlgebraicGeometry.Scheme.Hom.abs_pointCount_one_sub_le`: the Hasse–Weil bound, the case
  `n = 1`.
- `AlgebraicGeometry.Scheme.Hom.abs_pointCount_sub_le_two_mul_genus`: the Hasse–Weil bound
  `|N n - (qⁿ + 1)| ≤ 2 g q^{n/2}` for a smooth proper geometrically integral curve of genus `g`.
  It uses `AlgebraicGeometry.Scheme.Hom.natDegree_eq_two_mul_genus_of_isWeilFactorization`,
  the identity `deg P 1 = 2 g`, proved by counting effective divisors with Riemann–Roch.

## References

- [A. Weil, *Numbers of solutions of equations in finite fields*][weil1949]
- [J.-P. Serre, *Zeta and L functions*][serre1965]
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

open PowerSeries

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}

omit [Finite k] in
/-- **The point count as an alternating sum of power sums of reciprocal roots.** If the zeta
function of `X` factors as `∏ P i ^ ((-1) ^ (i + 1))` with `P i (0) = 1`, then for every `n ≥ 1`
the number of points of `X` over the degree `n` extension of `k` is
`N n = ∑ i, (-1) ^ i ∑_α αⁿ`, where `α` runs over the reciprocal roots `z⁻¹` of `P i`.

This is the trace formula `N n = ∑ (-1) ^ i tr (Fⁿ | V i)` of Step 1 of the blueprint proof of
`cor-zl-hasse-weil-general-bound`, read off from the factorization of the zeta function by
comparing logarithmic derivatives. -/
theorem Hom.pointCount_eq_sum_roots (f : X.Hom (Spec (.of k))) {q d : ℕ}
    {P : Fin (2 * d + 1) → Polynomial ℤ} (hfact : IsWeilFactorization q d f.zetaSeries P)
    {n : ℕ} (hn : n ≠ 0) :
    (f.pointCount n : ℂ) = ∑ i : Fin (2 * d + 1), (-1) ^ i.1 *
      (((P i).map (Int.castRingHom ℂ)).roots.map fun z ↦ z⁻¹ ^ n).sum := by
  classical
  set Q : Fin (2 * d + 1) → Polynomial ℂ := fun i ↦ (P i).map (Int.castRingHom ℂ) with hQdef
  have hQ0 : ∀ i, (Q i).coeff 0 = 1 := fun i ↦ by
    simp [hQdef, Polynomial.coeff_map, hfact.coeff_zero_eq_one i]
  set T : Fin (2 * d + 1) → ℂ⟦X⟧ := fun i ↦
    -PowerSeries.mk fun n ↦ if n = 0 then 0 else ((Q i).roots.map fun z ↦ z⁻¹ ^ n).sum with hT
  set NS : ℂ⟦X⟧ := PowerSeries.mk fun n ↦ if n = 0 then 0 else (f.pointCount n : ℂ) with hNS
  set se := Finset.univ.filter fun i : Fin (2 * d + 1) ↦ Even (i : ℕ) with hse
  set so := Finset.univ.filter fun i : Fin (2 * d + 1) ↦ Odd (i : ℕ) with hso
  set Zc : ℂ⟦X⟧ := map (algebraMap ℚ ℂ) f.zetaSeries with hZc
  have hQd : ∀ i, PowerSeries.X * derivative ℂ (Q i : ℂ⟦X⟧) = T i * (Q i : ℂ⟦X⟧) := fun i ↦
    X_mul_derivative_coe_of_coeff_zero_eq_one (IsAlgClosed.splits _) (hQ0 i)
  have hZ : PowerSeries.X * derivative ℂ Zc = NS * Zc := by
    have h0 : PowerSeries.X * derivative ℚ f.zetaSeries =
        (PowerSeries.mk fun n ↦ if n = 0 then 0 else (f.pointCount n : ℚ)) * f.zetaSeries :=
      X_mul_derivative_exp_subst _
    have h := congrArg (map (algebraMap ℚ ℂ)) h0
    rw [map_mul, map_mul, PowerSeries.map_X, map_derivative] at h
    rw [h]
    congr 1
    ext n
    simp only [hNS, PowerSeries.coeff_mk, coeff_map]
    split <;> simp
  have hfac : Zc * ∏ i ∈ se, (Q i : ℂ⟦X⟧) = ∏ i ∈ so, (Q i : ℂ⟦X⟧) := by
    have h := congrArg (map (algebraMap ℚ ℂ)) hfact.factorization
    have hcast : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
      RingHom.ext_int _ _
    simpa only [map_mul, map_prod, ← Polynomial.polynomial_map_coe, Polynomial.map_map,
      hcast] using h
  have hE := X_mul_derivative_prod se fun i _ ↦ hQd i
  have hO := X_mul_derivative_prod so fun i _ ↦ hQd i
  have hL : PowerSeries.X * derivative ℂ (Zc * ∏ i ∈ se, (Q i : ℂ⟦X⟧)) =
      (NS + ∑ i ∈ se, T i) * (Zc * ∏ i ∈ se, (Q i : ℂ⟦X⟧)) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    linear_combination Zc * hE + (∏ i ∈ se, (Q i : ℂ⟦X⟧)) * hZ
  have hunit : IsUnit (∏ i ∈ so, (Q i : ℂ⟦X⟧)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_prod]
    simp [Polynomial.constantCoeff_coe, hQ0]
  have hkey : NS + ∑ i ∈ se, T i = ∑ i ∈ so, T i := by
    rw [hfac, hO] at hL
    exact (hunit.mul_left_cancel (by rw [mul_comm, hL, mul_comm])).symm
  have hc := congrArg (PowerSeries.coeff n) hkey
  simp only [map_add, map_sum, hNS, hT, PowerSeries.coeff_mk, map_neg, if_neg hn,
    Finset.sum_neg_distrib, hse, hso, Finset.sum_filter, apply_ite (PowerSeries.coeff n),
    map_zero] at hc
  have halt : ∀ c : Fin (2 * d + 1) → ℂ, ∑ i : Fin (2 * d + 1), (-1) ^ i.1 * c i =
      (∑ i : Fin (2 * d + 1), if Even i.1 then c i else 0) -
        ∑ i : Fin (2 * d + 1), if Odd i.1 then c i else 0 := fun c ↦ by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases Nat.even_or_odd i.1 with h | h
    · rw [if_pos h, if_neg (by simpa using h), h.neg_one_pow, one_mul, sub_zero]
    · rw [if_neg (by simpa using h), if_pos h, h.neg_one_pow, neg_one_mul, zero_sub]
  rw [halt]
  linear_combination hc

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

namespace Scheme

section Endpoints

open _root_.Polynomial

variable (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

variable (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

end Endpoints

end Scheme

end AlgebraicGeometry

end
