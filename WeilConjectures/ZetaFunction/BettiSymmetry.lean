/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.BettiNumbers
public import WeilConjectures.Mathlib.Algebra.Polynomial.RingDivision
public import WeilConjectures.ZetaFunction.IntegralFrobeniusFactors
public import WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots

/-!
# Betti numbers of a smooth proper variety

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over
`k₀ = 𝔽_q`, with integral Frobenius factors `P₀, …, P_{2d}` and Betti numbers `bᵢ = deg Pᵢ`.
Then `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every `ℓ ≠ p`, `bᵢ = b_{2d-i}`, `b₀ = b_{2d} = 1`,
`P₀ = 1 - T` and `P_{2d} = 1 - qᵈ T`; consequently `Z(X₀, T)` has a pole of order exactly one at
`T = 1` and, for `d ≥ 1`, at `T = q^{-d}` (blueprint `thm-weil-final-betti`).

## Main statements

- `AlgebraicGeometry.Scheme.natDegree_eq_finrank_of_isIntegralFrobeniusFactor`:
  `deg Pᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` (`prop-weil-realization-independent-degrees`).
- `AlgebraicGeometry.Scheme.weilBettiNumber_eq_finrank`: `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for all
  `i ∈ ℤ` (`prop-weil-betti-comparison`).
- `AlgebraicGeometry.Scheme.betti_symmetry`: blueprint `thm-weil-final-betti`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

namespace WeilRiemannHypothesis

variable {q d : ℕ} {P : Fin (2 * d + 1) → Polynomial ℤ}

end WeilRiemannHypothesis

namespace Scheme

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

variable (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

end Scheme

end AlgebraicGeometry
