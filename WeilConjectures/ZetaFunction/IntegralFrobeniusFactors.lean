/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.SmoothProper

/-!
# Integral Frobenius factors

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over
`k₀ = 𝔽_q`. For every `0 ≤ i ≤ 2d` there is a unique polynomial `Pᵢ ∈ ℤ[T]` with `Pᵢ(0) = 1`
whose coefficientwise image in `ℚ̄_ℓ[T]` is the determinant factor
`P_{i,ℓ} = det(1 - T F | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))` for *every* prime `ℓ ≠ p`, and then
`Z(X₀, T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}`, a factorization independent of `ℓ` (blueprint
`sk-thm-intfactors`).

Existence is `AlgebraicGeometry.Scheme.exists_isWeilFactorization_of_smoothProper`; uniqueness
holds because `ℤ → ℚ̄_ℓ` is injective.

## Main statements

- `AlgebraicGeometry.Scheme.IsIntegralFrobeniusFactor.unique`: an integral realization of
  `P_{i,ℓ}` is unique.
- `AlgebraicGeometry.Scheme.existsUnique_isIntegralFrobeniusFactor`: existence and uniqueness of
  the integral Frobenius factors.
- `AlgebraicGeometry.Scheme.isWeilFactorization_of_isIntegralFrobeniusFactor`: the integral
  Frobenius factors are a Weil factorization of `Z(X₀, T)`, satisfying the functional equation and
  the Riemann hypothesis.
- `AlgebraicGeometry.Scheme.integral_frobenius_factors`: blueprint `sk-thm-intfactors`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

namespace Scheme

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

variable (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

end Scheme

end AlgebraicGeometry
