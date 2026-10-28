/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.Paper.FinitePositiveRootCharts

/-! # Power equivariance of the integral-reduced positive root charts

Source: finite-reduction-of-purity, Step 2, positive powers of the coefficient line.
(blueprint: lem-pur-finite-positive-root-chart-power).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The positive chart changes by the same scalar power as the ordered root chart.

Source: `thm-pur-finite-reduction-of-purity`, proof Step 2, invertible-twist
compatibility; the ordered basis normalization in
`def-pur-finite-positive-root-charts`.
(blueprint: lem-pur-finite-positive-root-chart-power).

Proof: let N = ell^n. On constant generators the root trivialization at
zeta = eta^a is a times the trivialization at eta. Its inverse at eta is thus
a times its inverse at zeta. The prescribed first-line site comparison is
independent of the root. Exact realization and its coefficient-unit comparison
therefore give the same equation for finiteTensorFirstChart. Full faithfulness
of the degree-zero single functor and the normalization of the first ordinary
chart give that equation for finiteTensorFirstSheafChart as well.
Work on a pro-etale cover where the first root generator supplies a coherent
frame. Under zeta = eta^a its degree-one generator changes by a, so its ordered
d-fold tensor changes by a^d. The positive chart is characterized by sending
these generators to one. Hence its value at eta is a^d times its value at zeta:
verify this on the generator in each frame and extend linearly. Such frames
exist locally since the first site comparison identifies the line with the
root line. The equality glues by the sheaf axiom. At d = 0 both normalized
charts send the coefficient-unit generator to one, and a^0 = 1. Finally the
additive single-complex functor and its fixed unit comparison preserve the
equality, giving the displayed derived-chart formula. The calculation is valid
on empty schemes and uses no finiteness or connectedness of T. -/
theorem finiteTensorPositiveChart_pow (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (d a : ℕ)
    (ζ η : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η P.diagonalExponent) (h : ζ = η ^ a) :
    (P.finiteTensorPositiveChart T η hη d).hom =
      a ^ d • (P.finiteTensorPositiveChart T ζ hζ d).hom := by sorry

end WeilConjectures.PurityFiniteSetting
