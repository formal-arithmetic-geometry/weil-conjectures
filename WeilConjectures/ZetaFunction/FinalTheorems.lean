/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EulerProduct
public import WeilConjectures.ZetaFunction.BettiSymmetry
public import WeilConjectures.ZetaFunction.DualityReciprocity
public import WeilConjectures.ZetaFunction.Rationality
public import WeilConjectures.ZetaLinearAlgebra.WeilNumbers

/-!
# The Weil conjectures for a smooth proper variety: the five assembled theorems

This file states the five Weil conjectures for a variety over the finite field `k₀ = 𝔽_q` in the
form of the blueprint (subsections `sk-thm-weil1` to `sk-thm-weil5`, nodes
`thm-weil-final-rationality`, `thm-weil-final-integrality`, `thm-weil-final-rh`,
`thm-weil-final-betti`, `thm-weil-final-functional-equation`), and the Riemann hypothesis in
its arithmetic form (`sk-thm-rh`, `prop-arithmetic-roots`).

The inputs are the trace formula, Poincaré duality and the weight estimate; their output is
`AlgebraicGeometry.Scheme.exists_isWeilFactorization_of_smoothProper`. The coefficients of the
zeta series are integral by the Euler product (`AlgebraicGeometry.Scheme.Hom.zetaSeries_eq_tprod`,
`AlgebraicGeometry.Scheme.Hom.exists_int_zetaSeries`) while the factorization is `ℓ`-adic by
construction; the two meet in the rationality descent and in the realization independence of the
integral factors (blueprint remarks `rem-zeta-where-this-feeds` and
`rationality-the-criterion-and-the-descent--remark-1`).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.weilRationality`: `sk-thm-weil1`, `thm-weil-final-rationality`.
- `AlgebraicGeometry.Scheme.weilIntegralFactors`: `sk-thm-weil2`, `thm-weil-final-integrality`.
- `AlgebraicGeometry.Scheme.riemannHypothesis`: `sk-thm-rh`, `prop-arithmetic-roots`,
  `sk-thm-weil3`, `thm-weil-final-rh`.
- `AlgebraicGeometry.Scheme.weilBetti`: `sk-thm-weil4`, `thm-weil-final-betti`.
- `AlgebraicGeometry.Scheme.weilFunctionalEquation`: `sk-thm-weil5`,
  `thm-weil-final-functional-equation`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

namespace Scheme

open scoped PowerSeries.WithPiTopology in
/-- Blueprint `sk-thm-weil1` and `thm-weil-final-rationality` (Weil conjectures I: rationality
and Euler product): for a scheme `X₀` of finite type over a finite field `k`,

* there are `A, B ∈ ℤ[T]` with `B(0) = 1` and `B(T) Z(X₀, T) = A(T)` in `ℚ⟦T⟧`;
* `Z(X₀, T) ∈ 1 + T ℤ⟦T⟧`;
* `Z(X₀, T) = ∏_{x ∈ |X₀|} (1 - T^{deg x})⁻¹`, the product over the closed points. -/
theorem Hom.weilRationality {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    (∃ A B : Polynomial ℤ, B.coeff 0 = 1 ∧
      f.zetaSeries * (B.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        (A.map (Int.castRingHom ℚ) : PowerSeries ℚ)) ∧
    (∃ Z : PowerSeries ℤ, PowerSeries.constantCoeff Z = 1 ∧
      PowerSeries.map (Int.castRingHom ℚ) Z = f.zetaSeries) ∧
    f.zetaSeries =
      ∏' x : X.finitePoints, (1 - PowerSeries.X ^ f.degreeOver x.1 : PowerSeries ℚ)⁻¹ :=
  sorry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `sk-thm-weil2` and `thm-weil-final-integrality` (Weil conjectures II: integral
Frobenius factors): for `X₀` smooth, proper and geometrically connected of pure dimension `d`,
for every `0 ≤ i ≤ 2d` there is a unique `Pᵢ ∈ ℤ[T]` with `Pᵢ(0) = 1` and
`Pᵢ^{(ℓ)} = det(1 - T F | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))` for every prime `ℓ ≠ p`, and these satisfy
`Z(X₀, T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}`, independently of `ℓ`. -/
theorem weilIntegralFactors :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      (∀ i, (P i).coeff 0 = 1 ∧ IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) ∧
      (∀ (i : Fin (2 * d + 1)) (Q : Polynomial ℤ), Q.coeff 0 = 1 →
        IsIntegralFrobeniusFactor k₀ X (i : ℕ) Q → Q = P i) ∧
      IsWeilFactorization (Nat.card k₀) d (X ↘ Spec (CommRingCat.of k₀)).zetaSeries P :=
  sorry

/-- Blueprint `sk-thm-rh`, `prop-arithmetic-roots`, `sk-thm-weil3` and `thm-weil-final-rh`
(the Riemann hypothesis): for `X₀` smooth, proper and geometrically connected of pure
dimension `d` and an integral Frobenius factor `P` in degree `i ≤ 2d`:

* every reciprocal root `α ∈ ℂ` of `P` (a root of `P^#(U) = U^{deg P} P(U⁻¹)`) is an algebraic
  integer and a `q`-Weil number of weight `i`: `|τ(α)| = q^{i/2}` for every embedding
  `τ : ℚ(α) → ℂ`;
* every ordinary root `β` (a root of `P`) is a `q`-Weil number of weight `-i`;
* for every prime `ℓ ≠ p`, the reciprocal roots of `P` in `ℚ̄_ℓ` are eigenvalues of the
  geometric Frobenius on `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`. -/
theorem riemannHypothesis {i : ℕ} (hi : i ≤ 2 * d) {P : Polynomial ℤ}
    (hP : IsIntegralFrobeniusFactor k₀ X i P) :
    (∀ α ∈ (P.reverse.map (Int.castRingHom ℂ)).roots,
      _root_.IsIntegral ℤ α ∧ IsWeilNumber (Nat.card k₀) i α) ∧
    (∀ β ∈ (P.map (Int.castRingHom ℂ)).roots, IsWeilNumber (Nat.card k₀) (-(i : ℝ)) β) ∧
    ∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)],
      ∀ α ∈ (P.reverse.map (Int.castRingHom (PadicAlgCl l))).roots,
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.HasEigenvalue α :=
  sorry

/-- Blueprint `sk-thm-weil4` and `thm-weil-final-betti` (Weil conjectures IV: Betti
symmetry): the integral Frobenius factors `Pᵢ` of `X₀` have degrees
`bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every `ℓ ≠ p`, `bᵢ = b_{2d-i}`, `b₀ = b_{2d} = 1`,
`P₀ = 1 - T`, `P_{2d} = 1 - qᵈ T`, and `Z(X₀, T)` has a pole of order exactly one at `T = 1`
and, if `d ≥ 1`, at `T = q^{-d}` (`AlgebraicGeometry.Scheme.bettiSymmetry`). -/
theorem weilBetti :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      (∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) ∧
      (∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (i : Fin (2 * d + 1)),
        (P i).natDegree = Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier) ∧
      (∀ i : Fin (2 * d + 1), (P i.rev).natDegree = (P i).natDegree) ∧
      (P 0).natDegree = 1 ∧ (P (Fin.last (2 * d))).natDegree = 1 ∧
      P 0 = 1 - Polynomial.X ∧
      P (Fin.last (2 * d)) = 1 - C ((Nat.card k₀ : ℤ) ^ d) * Polynomial.X :=
  sorry

/-- Blueprint `sk-thm-weil5` and `thm-weil-final-functional-equation` (Weil conjectures V:
functional equation): for the integral Frobenius factors `Pᵢ` of `X₀`, with
`χ = ∑ᵢ (-1)ⁱ deg Pᵢ`, the number `d χ` is even, `d χ = 2 m`, the sign `ε`
(`AlgebraicGeometry.weilSign`) is `±1`, and the rational function
`Z(X₀, T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}` satisfies

`Z(X₀, q^{-d} t⁻¹) = ε q^{m} t^χ Z(X₀, t)`

at every nonzero `t ∈ ℂ` at which no factor vanishes. -/
theorem weilFunctionalEquation :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      (∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) ∧
      ∃ m : ℤ, (d : ℤ) * Polynomial.alternatingNatDegreeSum P = 2 * m ∧
        (weilSign (Nat.card k₀) m P = 1 ∨ weilSign (Nat.card k₀) m P = -1) ∧
        ∀ t : ℂ, t ≠ 0 → (∀ i, ((P i).map (Int.castRingHom ℂ)).eval t ≠ 0) →
          Polynomial.alternatingProdEval (fun i ↦ (P i).map (Int.castRingHom ℂ))
              ((Nat.card k₀ : ℂ) ^ (-(d : ℤ)) * t⁻¹) =
            (weilSign (Nat.card k₀) m P : ℂ) * (Nat.card k₀ : ℂ) ^ m *
              t ^ Polynomial.alternatingNatDegreeSum P *
              Polynomial.alternatingProdEval (fun i ↦ (P i).map (Int.castRingHom ℂ)) t :=
  sorry

end Scheme

end AlgebraicGeometry
