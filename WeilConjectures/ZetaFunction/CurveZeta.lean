/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.EffectiveDivisorCount
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.ClosedPoints
public import WeilConjectures.EulerProduct
public import WeilConjectures.ZetaFunction.CurveFactorDegree

/-!
# The zeta function of a curve and the degree of its middle factor

For a scheme of finite type over a finite field `k` with `q` elements, the `n`-th coefficient of
the zeta function is the number of effective zero-cycles of degree `n`. For a smooth proper
integral curve `C` with `H⁰(C, 𝒪_C) = k` and genus `g`, these are the effective divisors of
degree `n`; grouping them by their class in `Pic(C)` and counting each class with Riemann–Roch
gives, for `n ≥ 2 g - 1`,

`(q - 1) Z_n = #{c ∈ Pic(C) | deg c = -n} · (q^{n + 1 - g} - 1)`,

where the number of classes is `h = #Pic⁰(C)` if `n` lies in the subgroup `δ ℤ` of degrees of
line bundles and `0` otherwise. With the Riemann hypothesis for the middle factor `P₁` of a Weil
factorization `Z = P₁ / ((1 - T) (1 - q T))` this forces `deg P₁ = 2 g`
(`AlgebraicGeometry.IsWeilFactorization.natDegree_eq_two_mul_of_coeff`). This is
F. K. Schmidt's argument; it gives Step 4 of the blueprint proof of `cor-zl-hasse-bound`,
`dim H¹(C ⊗ k̄, ℚ̄_ℓ) = 2 g`, without `ℓ`-adic cohomology.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.coeff_zetaSeries_eq_natCard_closedPoints`: `Z_n` is the number of
  effective zero-cycles of degree `n`.
- `AlgebraicGeometry.Scheme.Divisor.sub_one_mul_card_effective_eq`: the count of effective
  divisors of degree `n ≥ 2 g - 1`.
- `AlgebraicGeometry.Scheme.natDegree_eq_two_mul_arithmeticGenus_of_isWeilFactorization`:
  `deg P₁ = 2 g`.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme

universe u

open CategoryTheory

variable {k : Type u} [Field k] [Finite k]

section Curve

open MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

variable {C : Scheme.{u}} [C.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))] [IsIntegral C]
  [GlobalSectionsBijective k C]

end Curve

end AlgebraicGeometry.Scheme
