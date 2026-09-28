/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Statement
public import WeilConjectures.ZetaLinearAlgebra.Weights

/-!
# Uniqueness of the integral Frobenius factors

The second Weil conjecture asserts that the zeta function of a smooth proper geometrically
integral scheme of dimension `d` over a finite field with `q` elements factors as
`Z = ∏ᵢ P i ^ ((-1)^{i+1})` with `P i ∈ ℤ[T]` and `P i (0) = 1`, and that the factors are
unique.

Existence of the factorization is `AlgebraicGeometry.Scheme.weil_conjectures`, and for a pure
trace datum it is `TraceDatum.exists_isWeilFactorization`. What is added here is uniqueness:
under the Riemann hypothesis the reciprocal roots of `P i` have absolute value `q^{i/2}`, these
absolute values are pairwise distinct, and so the weights separate the factors. The general
form of that separation argument, for an arbitrary family of complex polynomials pure of
weights `0, 1, …, r`, is `Polynomial.eq_of_isPureOfWeight_of_prod_mul_eq`.

Uniqueness is what makes the `ℓ`-adic construction of the factors independent of `ℓ`: the
construction produces, for each prime `ℓ ≠ p`, a family satisfying these hypotheses, and any
two such families agree. That reading is a remark, not a statement of this file — nothing here
mentions `ℓ` or the `ℓ`-adic determinants.

This file formalises the uniqueness half of the integral-Frobenius-factors subsection of the
blueprint block on zeta functions and the Weil conjectures.

## Main statements

- `AlgebraicGeometry.IsWeilFactorization.unique`: two Weil factorizations of the same zeta
  function that both satisfy the Riemann hypothesis are equal.
- `AlgebraicGeometry.Scheme.existsUnique_weil_conjectures`: combined with existence, the Weil
  factors of a smooth proper geometrically integral scheme exist and are unique.

## References

- [P. Deligne, *La conjecture de Weil. I*][deligne1974]
- [J.-P. Serre, *Zeta and L functions*][serre1965]
-/

@[expose] public section

universe u

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

namespace Scheme

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The Weil conjectures, with uniqueness.** For a smooth proper geometrically integral
scheme of dimension `d` over a finite field, the family of integral Frobenius factors of the
zeta function satisfying the factorization, the functional equation and the Riemann hypothesis
exists and is unique. Existence is `AlgebraicGeometry.Scheme.weil_conjectures` and uniqueness
is `AlgebraicGeometry.IsWeilFactorization.unique`. -/
theorem existsUnique_weil_conjectures (hk : 1 < Nat.card k) (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsProper f] [GeometricallyIntegral f] :
    ∃! P : Fin (2 * d + 1) → Polynomial ℤ,
      IsWeilFactorization (Nat.card k) d f.zetaSeries P ∧
      WeilFunctionalEquation (Nat.card k) d P ∧
      WeilRiemannHypothesis (Nat.card k) d P := by
  obtain ⟨P, hP⟩ := Scheme.weil_conjectures f d
  exact ⟨P, hP, fun P' hP' ↦ (hP'.1.unique hk hP.1 hP'.2.2 hP.2.2)⟩

end Scheme

end AlgebraicGeometry

end
