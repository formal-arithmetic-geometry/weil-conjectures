/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance

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
`Sheaf.Paper.IntrinsicCoefficientTwists`.

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

/-- Reuse finiteness of the actual positive coefficient quotient and its size lift.
Source: blueprint fixed finite coefficient level
(blueprint: def-coefficient-twists-detailed). -/
instance diagonalCoefficientFinite (P : PurityFiniteSetting.{u}) : Finite P.Coefficient :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- Use the positive level itself as an annihilating l-power, without requiring the
ramification index to divide that level. Source: blueprint def-pur-conventions,
finite coefficients (blueprint: def-coefficient-twists-detailed). -/
def diagonalExponent (P : PurityFiniteSetting.{u}) : ℕ := P.coefficients.l ^ P.level

/-- This l-power annihilates the actual coefficient quotient and its size lift.
Source: blueprint finite coefficient conventions
(blueprint: def-coefficient-twists-detailed).
Proof: in O_E the valuation of l is the positive ramification index e. The valuation
of l^n is en, at least n, so l^n lies in (varpi^n). Its quotient image and its ULift
are zero. This uses n >= 1 and imposes no divisibility condition on n. -/
theorem diagonalExponent_annihilates (P : PurityFiniteSetting.{u}) :
    (P.diagonalExponent : P.Coefficient) = 0 := by
  sorry

/-- The same exponent is invertible on every k-scheme.
Source: blueprint finite coefficient conventions
(blueprint: def-coefficient-twists-detailed).
Proof: l differs from characteristic p, so its image in k is nonzero and is a unit.
Take its n-th power and apply the structure-map homomorphism on global sections.
This includes the empty scheme. -/
theorem diagonalExponent_isUnit (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) : IsUnit (P.diagonalExponent : Γ(T, ⊤)) := by
  sorry

/-- A(d)[2d] in the published ordered shifted-root-line presentation. Each factor
is mu_(l^n) tensor A, shifted by two; the zero-fold tensor is A in degree zero.
The finite line is the reduction of the roots-of-unity Tate line of the coefficient
conventions: extending mu_(l^n) to A is its usual finite-level presentation.
Source: blueprint def-coefficient-twists-detailed, positive powers
(blueprint: def-coefficient-twists-detailed). -/
def diagonalTwistEtale (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  Etale.affineLinearBaseCoefficient P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T d

/-- The same coefficient object on the actual small pro-etale site, using the
published comparison inverse image. The coefficient ring is the fixed quotient A.
Source: blueprint coefficient twists and finite comparison
(blueprint: def-coefficient-twists-detailed). -/
def diagonalTwist (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
    (P.diagonalTwistEtale T d)

end WeilConjectures.PurityFiniteSetting
