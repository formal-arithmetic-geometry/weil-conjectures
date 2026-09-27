/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Weil.Definitions

/-!
# Uniqueness of the integral Frobenius factors

The second Weil conjecture asserts that the zeta function of a smooth proper geometrically
integral scheme of dimension `d` over a finite field with `q` elements factors as
`Z = ∏ᵢ P i ^ ((-1)^{i+1})` with `P i ∈ ℤ[T]`, `P i (0) = 1`, and that the factors are
independent of the prime `ℓ` used to produce them.

Existence of the factorization is `AlgebraicGeometry.Scheme.weil_conjectures`, and for a pure
trace datum it is `TraceDatum.exists_isWeilFactorization`. What remains, and is the content of
the blueprint statement, is that the factors are *unique*: the reciprocal roots of `P i` have
absolute value `q^{i/2}`, these absolute values are pairwise distinct, and so the weights
separate the factors. Two families of integral factors of the same zeta function satisfying
the Riemann hypothesis therefore agree, which is exactly the independence of `ℓ`.

## Main statements

- `AlgebraicGeometry.IsWeilFactorization.eq_of_weilRiemannHypothesis`: uniqueness of the
  integral Frobenius factors.
-/

@[expose] public section

namespace AlgebraicGeometry

/-- Blueprint `sk-thm-intfactors`: Integral Frobenius factors.

The integral Frobenius factors of a zeta function are unique: if two families of integer
polynomials are Weil factorizations of the same power series and both satisfy the Riemann
hypothesis, then they are equal. Since the `ℓ`-adic construction produces, for each prime
`ℓ ≠ p`, a family satisfying these hypotheses, the factorization is independent of `ℓ`.
Existence is `AlgebraicGeometry.Scheme.weil_conjectures`. -/
theorem IsWeilFactorization.eq_of_weilRiemannHypothesis {q d : ℕ} (hq : 1 < q)
    {Z : PowerSeries ℚ} {P P' : Fin (2 * d + 1) → Polynomial ℤ}
    (h : IsWeilFactorization q d Z P) (h' : IsWeilFactorization q d Z P')
    (hrh : WeilRiemannHypothesis q d P) (hrh' : WeilRiemannHypothesis q d P') :
    P = P' :=
  sorry

end AlgebraicGeometry

end
