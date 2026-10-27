/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.Paper.FiniteReductionRootCharts

/-! # Power equivariance of the published finite root charts

Source: finite-reduction-of-purity, Step 2, ordered powers of the root-line chart.
(blueprint: lem-pur-finite-published-root-chart-power).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Raising the root to a power rescales the inverse root chart by that power,
and rescales its ordered d-fold tensor by the d-th power of that scalar.

Source: `thm-pur-finite-reduction-of-purity`, proof Step 2, invertible-twist
compatibility; the ordered tensor construction in
`def-pur-finite-reduction-root-charts`.
(blueprint: lem-pur-finite-published-root-chart-power).

Proof: write N = ell^n. The section formula for the root trivialization sends a
constant coefficient b to b tensor the root. If zeta = eta^a, the trivialization
at zeta is a times the one at eta, because the roots group law is addition in
its associated Z/N-module. Compose with their inverse isomorphisms to get that
the inverse chart at eta is a times that at zeta. The single-complex functor and
the degree-two shift are additive, so the shifted degree-one charts obey the
same equation. Induct on d in finiteReductionOrderedPower. The zero chart is
independent of the root and a^0 = 1. At a successor, bilinearity of the derived
tensor changes the scalar a^d to a^d * a = a^(d+1); all reassociation, shift
and unit maps are fixed. Exact comparison pullback is additive. Composing with
its fixed shift comparison therefore preserves the equation and gives the
stated pro-etale chart. Empty schemes obey the same equations. Both roots are
primitive, so every root trivialization used in the argument is invertible. -/
theorem finiteReductionPowerTrivialization_pow (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (d a : ℕ)
    (ζ η : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η P.diagonalExponent) (h : ζ = η ^ a) :
    (P.finiteReductionPowerTrivialization T η hη d).hom =
      a ^ d • (P.finiteReductionPowerTrivialization T ζ hζ d).hom := by sorry

end WeilConjectures.PurityFiniteSetting
