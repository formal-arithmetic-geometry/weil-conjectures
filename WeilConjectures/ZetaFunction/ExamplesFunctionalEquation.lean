/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.ClassicalFunctionalEquation
public import WeilConjectures.ZetaFunction.Examples

/-!
# The functional equation of the projective line

For `X₀ = ℙ¹` over a finite field `k = 𝔽_q`, the integral Frobenius factors are
`P₀ = 1 - T`, `P₁ = 1`, `P₂ = 1 - qT` (`AlgebraicGeometry.isWeilFactorization_projectiveLine`,
`AlgebraicGeometry.isIntegralFrobeniusFactor_projectiveLine`), so `d = 1`, `b₀ = b₂ = 1`,
`b₁ = 0`, `χ = 2`, `D = D₀ D₂ = 1 · q = q` and `ε = 1`; here `D₀ = det(F₀)` is checked on
`H⁰`, while `D₂ = det(F₂)` is computed from the factor `P₂`. The functional equation
`Z(ℙ¹, 1/(qT)) = q T² Z(ℙ¹, T)` is checked directly on the rational function
`Z(ℙ¹, T) = ((1 - T)(1 - qT))⁻¹` (`AlgebraicGeometry.zetaSeries_projectiveLine`). This is
blueprint `example-functional-equation-projective-line`.

## Main statements

- `AlgebraicGeometry.alternatingNatDegreeSum_projectiveLine`: `χ = 2`.
- `AlgebraicGeometry.weilDeterminantConstant_projectiveLine`: `D₀ = D₁ = 1`, `D₂ = q`.
- `AlgebraicGeometry.det_frobeniusEnd_cohomology_zero_projectiveLine`: `det(F₀) = 1`.
- `AlgebraicGeometry.weilDeterminantScalar_projectiveLine`: `D = q`.
- `AlgebraicGeometry.weilSign_projectiveLine`: `ε = 1`.
- `AlgebraicGeometry.alternatingProdEval_projectiveLine`: `Z(ℙ¹, 1/(qt)) = q t² Z(ℙ¹, t)`.
-/

@[expose] public section

universe u

open Polynomial

namespace AlgebraicGeometry

variable (k : Type u) [Field k] [Finite k]

/-- The Euler characteristic of the projective line: `χ = b₀ - b₁ + b₂ = 1 - 0 + 1 = 2`
(blueprint `example-functional-equation-projective-line`). -/
theorem alternatingNatDegreeSum_projectiveLine :
    alternatingNatDegreeSum ![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] = 2 := by
  obtain ⟨-, h0, h1, h2⟩ := isWeilFactorization_projectiveLine k
  simp only [weilBettiNumber] at h0 h1 h2
  rw [alternatingNatDegreeSum, Fin.sum_univ_three]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  simp_all

/-- The determinant constants `Dᵢ = (-1)^{bᵢ} [T^{bᵢ}] Pᵢ` of the integral Frobenius factors
`P₀ = 1 - T`, `P₁ = 1`, `P₂ = 1 - qT` of the projective line are `D₀ = 1`, `D₁ = 1`, `D₂ = q`
(blueprint `example-functional-equation-projective-line`). -/
theorem weilDeterminantConstant_projectiveLine :
    weilDeterminantConstant (1 - X : ℤ[X]) = 1 ∧ weilDeterminantConstant (1 : ℤ[X]) = 1 ∧
      weilDeterminantConstant (1 - C (Nat.card k : ℤ) * X) = Nat.card k := by
  have hq : (Nat.card k : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hd0 : (1 - X : ℤ[X]).natDegree = 1 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt (by simp), natDegree_X]
  have hd2 : (1 - C (Nat.card k : ℤ) * X).natDegree = 1 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt (by
      rw [natDegree_one, natDegree_C_mul_X _ hq]; norm_num), natDegree_C_mul_X _ hq]
  refine ⟨by simp [weilDeterminantConstant, hd0, coeff_one],
    by simp [weilDeterminantConstant], ?_⟩
  rw [weilDeterminantConstant, hd2]
  simp [coeff_one]

/-- The determinant of geometric Frobenius on `H⁰(ℙ¹ ⊗ k̄, ℚ̄_ℓ)` is `det(F₀) = 1`, the
determinant constant `D₀` of `P₀ = 1 - T`: Frobenius acts on `H⁰` of the geometrically
connected `ℙ¹` as the identity (blueprint `example-functional-equation-projective-line`). -/
theorem det_frobeniusEnd_cohomology_zero_projectiveLine (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k ≠ l)] :
    LinearMap.det ((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology
        0).frobeniusEnd = 1 := by
  rw [FrobeniusModule.frobeniusEnd, WeilSheaf.frobenius_cohomology_zero_adicConstant,
    LinearEquiv.refl_toLinearMap, LinearMap.det_id]

/-- The determinant scalar of the projective line:
`D = ∏ᵢ Dᵢ^{(-1)ⁱ} = 1 · 1⁻¹ · q = q` (blueprint `example-functional-equation-projective-line`). -/
theorem weilDeterminantScalar_projectiveLine :
    weilDeterminantScalar ![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] = Nat.card k := by
  obtain ⟨hD0, hD1, hD2⟩ := weilDeterminantConstant_projectiveLine k
  have e0 : (![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] : Fin 3 → ℤ[X]) 0 = 1 - X := rfl
  have e1 : (![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] : Fin 3 → ℤ[X]) 1 = 1 := rfl
  have e2 : (![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] : Fin 3 → ℤ[X]) 2 =
      1 - C (Nat.card k : ℤ) * X := rfl
  rw [weilDeterminantScalar, Fin.prod_univ_three, e0, e1, e2, hD0, hD1, hD2]
  norm_num

/-- The sign of the functional equation of the projective line: with `d = 1`, `χ = 2` and
`m = d χ / 2 = 1`, `ε = (-1)^χ q^{-m} D = q⁻¹ q = 1`
(blueprint `example-functional-equation-projective-line`). -/
theorem weilSign_projectiveLine :
    weilSign (Nat.card k) 1 ![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] = 1 := by
  have hq : (Nat.card k : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hD := weilDeterminantScalar_projectiveLine k
  rw [weilDeterminantScalar] at hD
  simp only [weilDeterminantConstant, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] at hD
  rw [weilSign, alternatingNatDegreeSum_projectiveLine]
  simp only [leadingCoeff]
  rw [hD, zpow_neg_one]
  simp [hq]

/-- Blueprint `example-functional-equation-projective-line`: the rational function
`Z(ℙ¹, t) = ((1 - t)(1 - qt))⁻¹`, written as the alternating product `∏ᵢ Pᵢ(t)^{(-1)^{i+1}}` of
the integral Frobenius factors of `ℙ¹`, satisfies the functional equation

`Z(ℙ¹, 1/(qt)) = q t² Z(ℙ¹, t)`

at every nonzero `t ∈ ℂ`; here `q t² = ε q^{d χ / 2} t^χ` with `ε = 1`, `d = 1`, `χ = 2`
(`AlgebraicGeometry.weilSign_projectiveLine`,
`AlgebraicGeometry.alternatingNatDegreeSum_projectiveLine`). The power series `Z(ℙ¹, T)` is the
expansion of this rational function (`AlgebraicGeometry.zetaSeries_projectiveLine`). -/
theorem alternatingProdEval_projectiveLine (t : ℂ) (ht : t ≠ 0) :
    alternatingProdEval (fun i ↦ (![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] i).map
        (Int.castRingHom ℂ)) ((Nat.card k : ℂ) ^ (-(1 : ℤ)) * t⁻¹) =
      (Nat.card k : ℂ) * t ^ 2 * alternatingProdEval
        (fun i ↦ (![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] i).map (Int.castRingHom ℂ)) t := by
  have hq : (Nat.card k : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [alternatingProdEval, alternatingProdEval, Fin.prod_univ_three, Fin.prod_univ_three]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Fin.val_zero, Fin.val_one, Fin.val_two, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_X, eval_sub,
    eval_one, eval_X, eq_intCast, Int.cast_natCast, zpow_neg_one]
  norm_num
  have h1 : (1 - (Nat.card k : ℂ)⁻¹ * t⁻¹) = ((Nat.card k : ℂ) * t - 1) /
      ((Nat.card k : ℂ) * t) := by field_simp
  have h2 : (1 - (Nat.card k : ℂ) * ((Nat.card k : ℂ)⁻¹ * t⁻¹)) = (t - 1) / t := by
    field_simp
  rw [h1, h2, inv_div, inv_div, div_mul_div_comm, div_eq_mul_inv, ← mul_inv]
  rw [show (1 - t) = -(t - 1) by ring, show (1 - (Nat.card k : ℂ) * t) =
    -((Nat.card k : ℂ) * t - 1) by ring, neg_mul_neg]
  ring

/-- Blueprint `example-functional-equation-projective-line`: the functional equation of the
projective line in the predicted shape `Z(ℙ¹, 1/(q^d t)) = ε q^{m} t^χ Z(ℙ¹, t)` of
`AlgebraicGeometry.Scheme.weil_functional_equation`, with `d = 1`, `χ = 2`, `m = d χ / 2 = 1`
and `ε = 1`. -/
theorem functionalEquation_projectiveLine :
    (1 : ℤ) * alternatingNatDegreeSum ![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] = 2 * 1 ∧
      weilSign (Nat.card k) 1 ![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] = 1 ∧
      ∀ t : ℂ, t ≠ 0 →
        alternatingProdEval (fun i ↦ (![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] i).map
            (Int.castRingHom ℂ)) ((Nat.card k : ℂ) ^ (-(1 : ℤ)) * t⁻¹) =
          (weilSign (Nat.card k) 1 ![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] : ℂ) *
            (Nat.card k : ℂ) ^ (1 : ℤ) *
            t ^ alternatingNatDegreeSum ![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] *
            alternatingProdEval (fun i ↦ (![1 - X, 1, 1 - C (Nat.card k : ℤ) * X] i).map
              (Int.castRingHom ℂ)) t := by
  refine ⟨by rw [alternatingNatDegreeSum_projectiveLine]; rfl, weilSign_projectiveLine k,
    fun t ht ↦ ?_⟩
  rw [alternatingProdEval_projectiveLine k t ht, weilSign_projectiveLine,
    alternatingNatDegreeSum_projectiveLine]
  push_cast
  rw [zpow_one, zpow_two]
  ring

end AlgebraicGeometry
