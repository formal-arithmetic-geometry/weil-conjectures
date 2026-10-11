/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.TraceFormula
public import WeilConjectures.ZetaIntegrality
public import WeilConjectures.ZetaLinearAlgebra.Rationality

/-!
# Rationality of the zeta function

Let `X₀` be a scheme of finite type over the finite field `k₀ = 𝔽_q`. Then its zeta series
`Z(X₀, T)` is a rational function: `B(T) Z(X₀, T) = A(T)` for integer polynomials `A, B` with
`B(0) = 1` (blueprint `sk-thm-rationality`).

For `X₀` separated, the Grothendieck–Lefschetz trace formula with compact supports
(`AlgebraicGeometry.WeilSheaf.pointCount_eq_finsum_trace_compactlySupportedCohomology`) writes
the point counts as alternating traces on the finitely many nonzero groups
`H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)`, so `Z(X₀, T)` is an alternating product of determinants over `ℚ̄_ℓ`; its
coefficients are integers by the Euler product, and the Hankel rank criterion descends
rationality from `ℚ̄_ℓ` to `ℚ` (`AlgebraicGeometry.Scheme.Hom.zetaSeries_rational_of_traceDatum`).
A general `X₀` of finite type is covered by finitely many affine opens, and the zeta series is
multiplicative for the decomposition of `X₀` into an open subscheme and its closed complement.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_int_mul_zetaSeries_eq`: rationality of the zeta series of
  a scheme of finite type over a finite field (`sk-thm-rationality`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}

/-- Blueprint `sk-thm-rationality` (rationality of the zeta series): for a scheme `X₀` of finite
type (quasi-compact and locally of finite type) over a finite field `k`, there are integer
polynomials `A, B` with `B(0) = 1` and `B(T) Z(X₀, T) = A(T)` in `ℚ⟦T⟧`. -/
theorem Hom.exists_int_mul_zetaSeries_eq (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] :
    ∃ A B : Polynomial ℤ, B.coeff 0 = 1 ∧
      f.zetaSeries * (B.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        (A.map (Int.castRingHom ℚ) : PowerSeries ℚ) :=
  sorry

end AlgebraicGeometry.Scheme
