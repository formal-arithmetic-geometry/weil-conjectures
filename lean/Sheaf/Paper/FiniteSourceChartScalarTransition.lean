/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Sheaf.Paper.FiniteReductionRootCharts

/-! # A uniform scalar for changes of finite purity source charts

Source: the root-chart calculation in def-pur-smooth-pullback-exchange.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Changing the primitive root rescales all source charts by the same integer.
Source: def-pur-smooth-pullback-exchange, middle identification and root-chart
normalization; def-pur-finite-reduction-root-charts, ordered tensor construction
(blueprint: lem-pur-finite-source-chart-scalar-transition).

Proof: put N = ell^n. Write eta = zeta^a, with a prime to N, and choose a natural
number c with ac = 1 modulo N. The section-normalized degree-one trivialization
from the constant module to the root line at eta is a times the one at zeta:
this follows on scalar-unit generators because the roots group law becomes
addition in its associated Z/N-module. The inverse trivializations therefore
satisfy t_eta = c times t_zeta, since N annihilates the coefficient ring.
The degree-one shifted chart uses this inverse. Induct on the ordered tensor
recursion: its zero term is the unit comparison, and bilinearity at a successor
multiplies the scalar by c. The degree-d chart consequently changes by c^d.
All reassociation and tensor-unit comparisons are the same for both roots.
Tensoring with an arbitrary complex, exact comparison pullback, realization,
and shift preserve integer scalar multiplication. Thus the source chart at eta
is c^d times the source chart at zeta. Compose on the left with the inverse
zeta chart to obtain the displayed equality, with r = c^d, simultaneously for
all schemes, maps and complexes. For d = 0 take r = 1; on an empty scheme or
a zero complex the same equation holds because its identity is zero.
-/
theorem exists_finiteReductionSourceChartScalar (P : PurityFiniteSetting.{u})
    (d : ℕ) (ζ η : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η P.diagonalExponent) :
    ∃ r : ℕ, ∀ {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
      (f : X ⟶ Y) (K : Scheme.proEtaleDerivedCategory Y P.Ring),
      (P.finiteReductionSourceTrivialization f d ζ hζ K).inv ≫
        (P.finiteReductionSourceTrivialization f d η hη K).hom =
          r • 𝟙 (((P.finiteReductionPullback f).obj K)⟦2 * (d : ℤ)⟧) := by sorry

end WeilConjectures.PurityFiniteSetting
