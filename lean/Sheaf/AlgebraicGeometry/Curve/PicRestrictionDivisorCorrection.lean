/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard

/-!
# Principal correction gives a boundary-supported representative

Source: blueprint, sec-curve-estimates/sk-prop-cd-affine/lem-sc-pic-affine,
first paragraph, restriction and boundary divisors
(blueprint: lem-sc-pic-restriction-divisor-correction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A divisor whose class restricts trivially has a boundary-supported representative.
Source: blueprint, sec-curve-estimates/sk-prop-cd-affine/lem-sc-pic-affine, first paragraph;
restriction and boundary divisors, steps 2--4 of lem-sc-pic-restriction-exact
(blueprint: lem-sc-pic-restriction-divisor-correction).

Proof: Restrict D by retaining its coefficients at the points of C. The divisor-class
comparison identifies its class with the pullback of O(D), since the open immersion
identifies local rings and valuation bounds. The assumed triviality means that this
restricted divisor is principal, div_C(a), by injectivity of the divisor-class comparison.
The dense open immersion identifies the two function fields. Regard the same nonzero
rational function a as a function on c.Z. Its orders at points of C agree with those of a
on C, since their local rings are identified. Set E = D - div_Z(a). Its coefficients at
all points in the image vanish, and its Picard class equals that of D because principal
divisors have trivial class. Both divisors have finite support on the Noetherian curves.
If the boundary is empty this construction forces E = 0, as required. The conclusion is
only a divisor normal form; generation of the Picard kernel is proved separately. -/
theorem Scheme.Hom.pic_restriction_divisor_correction
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    (D : c.Z.Divisor)
    (hD : Scheme.Pic.mapHom c.i
      (@Scheme.Divisor.toPic k _ c.Z ⟨c.g⟩ hsm D).toMul = 1) :
    ∃ E : c.Z.Divisor,
      @Scheme.Divisor.toPic k _ c.Z ⟨c.g⟩ hsm E =
        @Scheme.Divisor.toPic k _ c.Z ⟨c.g⟩ hsm D ∧
      ∀ P : closedPoints c.Z, P.val ∈ Set.range c.i.base → E P = 0 := by sorry

end AlgebraicGeometry
