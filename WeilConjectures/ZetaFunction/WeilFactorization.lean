/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Weil.Definitions
public import WeilConjectures.ZetaLinearAlgebra.Weights

/-!
# Uniqueness of Weil factorizations

Under the Riemann hypothesis the reciprocal roots of the `i`-th factor of a Weil factorization
have absolute value `q^{i/2}`; these absolute values are pairwise distinct, so the weights
separate the factors and a Weil factorization of a given power series satisfying the Riemann
hypothesis is unique. The general form of the separation argument, for an arbitrary family of
complex polynomials pure of weights `0, 1, …, r`, is
`Polynomial.eq_of_isPureOfWeight_of_prod_mul_eq`.

## Main statements

- `AlgebraicGeometry.IsWeilFactorization.unique`: two Weil factorizations of the same power
  series that both satisfy the Riemann hypothesis are equal.
-/

@[expose] public section

namespace AlgebraicGeometry

/-- **Uniqueness of the integral Frobenius factors.** If two families of integer polynomials
are Weil factorizations of the same power series and both satisfy the Riemann hypothesis, then
they are equal: a reciprocal root of absolute value `q^{i/2}` can only come from the degree-`i`
member of either family. -/
theorem IsWeilFactorization.unique {q d : ℕ} (hq : 1 < q) {Z : PowerSeries ℚ}
    {P P' : Fin (2 * d + 1) → Polynomial ℤ}
    (h : IsWeilFactorization q d Z P) (h' : IsWeilFactorization q d Z P')
    (hrh : WeilRiemannHypothesis q d P) (hrh' : WeilRiemannHypothesis q d P') :
    P = P' := by
  classical
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hpure : ∀ (Q : Fin (2 * d + 1) → Polynomial ℤ), (∀ i, (Q i).coeff 0 = 1) →
      WeilRiemannHypothesis q d Q →
      ∀ i, ((Q i).map (Int.castRingHom ℂ)).IsPureOfWeight q i.1 := by
    intro Q hQ0 hQrh i
    exact ⟨by rw [Polynomial.coeff_map, hQ0 i]; simp, hQrh i⟩
  -- the two families have the same alternating product, as an identity of rational polynomials
  have hcoe : ∀ (Q : Fin (2 * d + 1) → Polynomial ℤ) (s : Finset (Fin (2 * d + 1))),
      ((∏ i ∈ s, (Q i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) =
        ∏ i ∈ s, (((Q i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) := by
    intro Q s
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ Polynomial.coeToPowerSeries.ringHom_apply
  have hQ : (∏ i ∈ Finset.univ.filter fun i : Fin (2 * d + 1) ↦ Odd i.1,
        (P i).map (Int.castRingHom ℚ)) *
      (∏ i ∈ Finset.univ.filter fun i : Fin (2 * d + 1) ↦ Even i.1,
        (P' i).map (Int.castRingHom ℚ)) =
      (∏ i ∈ Finset.univ.filter fun i : Fin (2 * d + 1) ↦ Odd i.1,
        (P' i).map (Int.castRingHom ℚ)) *
      (∏ i ∈ Finset.univ.filter fun i : Fin (2 * d + 1) ↦ Even i.1,
        (P i).map (Int.castRingHom ℚ)) := by
    refine Polynomial.coe_injective ℚ ?_
    rw [Polynomial.coe_mul, Polynomial.coe_mul, hcoe, hcoe, hcoe, hcoe, ← h.factorization,
      ← h'.factorization]
    ring
  have hcast : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  have hcross := congrArg (Polynomial.map (algebraMap ℚ ℂ)) hQ
  simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_map, hcast] at hcross
  have hmap := Polynomial.eq_of_isPureOfWeight_of_prod_mul_eq hq
    (hpure P h.coeff_zero_eq_one hrh) (hpure P' h'.coeff_zero_eq_one hrh') hcross
  funext i
  exact Polynomial.map_injective _ hinj (congrFun hmap i)

end AlgebraicGeometry
