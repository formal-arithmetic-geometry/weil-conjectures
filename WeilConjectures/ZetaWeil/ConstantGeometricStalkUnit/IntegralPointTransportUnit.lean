/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates

/-! # One-step point transport on the completed regular coefficient unit

Source: the constant-sheaf clause of `prop-every-iterate-trace`, reviewed expansion
steps 6--7 (blueprint: lem-zl-integral-point-transport-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.ConstantGeometricStalkUnit

/-- One integral restriction-and-coprojection transport preserves the completed unit.
Source: the constant-sheaf clause of `prop-every-iterate-trace`, reviewed expansion
steps 6--7 (blueprint: lem-zl-integral-point-transport-unit).

Proof: take the strict system of regular finite coefficient modules in degree zero.
At every level, restriction along point Frobenius, its inverse-image coprojection,
and multiplication preserve each constant section. These equations commute with
the actual quotient maps, so they give the identity map of the whole strict system.
The completed constant object is its normalized Roos realization, with zero shifted
component and quotient projections. The whole-system transport realization theorem
identifies the realized transport with the specified integral transport. The canonical
coefficient pullback comparison identifies its unit multiplication with integralUnit.
Naturality of the realization and of its section comparison now sends the strict
system identity to the displayed derived identity on the completed regular object.
No claim of faithfulness for a family of individual finite reductions is used. -/
theorem integralPointTransport_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    frobeniusPointTransportIntegral D l hl E
        (integralConstantCoefficientObject l E (Spec (.of D.k))) ≫
      (pointFibreIntegralAmbient D l E).map
        (integralUnit l E (frobeniusPointIso D).hom).hom = 𝟙 _ := by
  sorry

end WeilConjectures.ConstantGeometricStalkUnit
