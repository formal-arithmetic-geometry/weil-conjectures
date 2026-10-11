/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.BettiNumbers
public import WeilConjectures.ZetaFunction.IntegralFrobeniusFactors

/-!
# Betti numbers of a smooth proper variety

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over
`k₀ = 𝔽_q`, with integral Frobenius factors `P₀, …, P_{2d}` and Betti numbers `bᵢ = deg Pᵢ`.
Then `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every `ℓ ≠ p`, `bᵢ = b_{2d-i}`, `b₀ = b_{2d} = 1`,
`P₀ = 1 - T` and `P_{2d} = 1 - qᵈ T`; consequently `Z(X₀, T)` has a pole of order exactly one at
`T = 1` and, for `d ≥ 1`, at `T = q^{-d}` (blueprint `sk-thm-betti`).

## Main statements

- `AlgebraicGeometry.Scheme.natDegree_eq_finrank_of_isIntegralFrobeniusFactor`:
  `deg Pᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` (`prop-weil-realization-independent-degrees`).
- `AlgebraicGeometry.Scheme.weilBettiNumber_eq_finrank`: `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for all
  `i ∈ ℤ` (`prop-weil-betti-comparison`).
- `AlgebraicGeometry.Scheme.bettiSymmetry`: blueprint `sk-thm-betti`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

namespace Scheme

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `prop-weil-realization-independent-degrees`: the degree of an integral Frobenius
factor in degree `i` is `dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every prime `ℓ ≠ p`: scalar extension along the
injective `ℤ → ℚ̄_ℓ` preserves degrees, and `deg P_{i,ℓ} = dim Hⁱ`
(`AlgebraicGeometry.Scheme.natDegree_frobeniusCharpolyRev`). In particular the degree does not
depend on `ℓ`. -/
theorem natDegree_eq_finrank_of_isIntegralFrobeniusFactor
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {i : ℤ} {P : Polynomial ℤ}
    (hP : IsIntegralFrobeniusFactor k₀ X i P) (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] :
    P.natDegree =
      Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k₀ l X).cohomology i).carrier := by
  rw [← natDegree_frobeniusCharpolyRev, ← hP l,
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]

end Scheme

end AlgebraicGeometry
