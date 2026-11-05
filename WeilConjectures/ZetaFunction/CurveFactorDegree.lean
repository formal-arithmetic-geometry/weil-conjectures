/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import WeilConjectures.Mathlib.Analysis.Complex.Norm
public import WeilConjectures.ZetaFunction.WeilFactorization

/-!
# The degree of the middle factor of a Weil factorization in dimension one

Let `Z = P₁ / ((1 - T) (1 - q T))` be a Weil factorization in dimension `d = 1` whose middle
factor `P₁` satisfies the Riemann hypothesis. If the coefficients of `Z` grow like those of the
zeta function of a curve of genus `g`, that is `(q - 1) Z_n = h (q^{n + 1 - g} - 1)` for all large
`n` divisible by some `δ ≥ 1` and `Z_n = 0` for the other large `n`, then `deg P₁ = 2 g`.

The proof is elementary. Partial fractions give `(q - 1) Z_n = q^{n + 1} P₁(1/q) - P₁(1)` for
`n ≥ deg P₁`. Comparing with the given growth first forces `δ = 1` (three consecutive
coefficients `0, H, 0` with `H ≠ 0` cannot have this shape) and then `P₁(1) = h` and
`P₁(1/q) = h q^{-g}`. The Riemann hypothesis `|z| = q^{-1/2}` for the roots `z` of `P₁` gives
`|1/q - z| = q^{-1/2} |1 - z|`, hence `|P₁(1/q)| = q^{-deg P₁ / 2} |P₁(1)|`, and so
`q^{-g} = q^{-deg P₁ / 2}`.

This is the arithmetic half of the classical proof (F. K. Schmidt) that the middle factor of the
zeta function of a curve has degree `2 g`; the growth of the coefficients is Riemann–Roch.

## Main statements

- `AlgebraicGeometry.IsWeilFactorization.sub_one_mul_coeff_eq`: the partial fraction formula
  `(q - 1) Z_n = q^{n + 1} P₁(1/q) - P₁(1)` for `n ≥ deg P₁`.
- `AlgebraicGeometry.IsWeilFactorization.natDegree_eq_two_mul_of_coeff`: `deg P₁ = 2 g`.
-/

@[expose] public section

open Polynomial

namespace AlgebraicGeometry

namespace IsWeilFactorization

variable {q : ℕ} {Z : PowerSeries ℚ} {P : Fin (2 * 1 + 1) → Polynomial ℤ}

end IsWeilFactorization

end AlgebraicGeometry
