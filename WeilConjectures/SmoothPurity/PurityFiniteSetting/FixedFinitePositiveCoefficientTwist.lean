/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceLinearTraceInvariance
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra

/-! # The positive finite coefficient twist in fixed-ring coordinates

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sp-tate-twist,
def-coefficient-twists-detailed, finite reduction and tensor-power clauses
(blueprint: def-coefficient-twists-detailed).

The recorded intrinsic interface reexports signed finite twists as modules over a
coefficient ring sheaf. This module exposes their positive shifted presentation in
fixed-ring module sheaves, as required by the recorded finite exceptional functor.
The first line is the published root line mu_(l^n) tensor A; its d-th tensor power
with shift 2d is the published ordered affineLinearBaseCoefficient. No generator,
orientation or root of unity is chosen. The exponent l^n kills O_E/(varpi^n) at
every positive level, including levels not divisible by the ramification index.
The intrinsic signed, integral, rational and Qbar definitions are provided by
`WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists`.

## Main declarations

- `diagonalExponent`: a valid annihilator at every positive finite level.
- `diagonalTwistEtale`: the existing shifted positive root-line tensor power.
- `diagonalTwist`: its exact inverse image on the small pro-etale site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

end WeilConjectures.PurityFiniteSetting
