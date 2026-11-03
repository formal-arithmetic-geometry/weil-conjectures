/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.Basic

/-! # Finite-coefficient Kummer classes

Source: literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/
sk-prop-an/pur9-def-kummer-class (blueprint: pur9-def-kummer-class).

The main definition realizes the finite-coefficient Kummer boundary using the canonical
derived Kummer morphism and the finite purity coefficient datum. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
/-- The coefficient ring of a finite purity setting has nonzero characteristic.
Source: blueprint sec-smooth-purity/sk-prop-an/pur9-def-kummer-class
(blueprint: pur9-def-kummer-class).
Proof: A is finite (`diagonalCoefficientFinite`), so its characteristic is nonzero by
Mathlib `CharP.ringChar_ne_zero_of_finite`. Alternatively, ell^n is zero in A by
`diagonalExponent_annihilates`, so the characteristic divides ell^n > 0. -/
theorem coefficientNeZero (P : PurityFiniteSetting.{u}) :
    NeZero (ringChar P.Coefficient) :=
  ⟨CharP.ringChar_ne_zero_of_finite P.Coefficient⟩
/-- The finite coefficient ring has an invertible exponent on every k-scheme.
Source: blueprint sec-smooth-purity/sk-prop-an/pur9-def-kummer-class
(blueprint: pur9-def-kummer-class).
Proof: take the admissible exponent ell^n = `diagonalExponent`. It is positive because
ell is prime, and it annihilates A by `diagonalExponent_annihilates`. It is a unit in
the global sections of W by `diagonalExponent_isUnit` applied to the structure morphism
aW, since ell differs from the characteristic of k; this includes the empty scheme. -/
theorem coefficientHasInvertibleExponent (P : PurityFiniteSetting.{u})
    (W : Scheme.{u}) (aW : W ⟶ Spec (.of P.field.k)) :
    HasInvertibleExponent P.Coefficient W := by
  refine ⟨P.diagonalExponent, ?_, P.diagonalExponent_annihilates, ?_⟩
  · exact pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level
  · exact P.diagonalExponent_isUnit aW
end WeilConjectures.PurityFiniteSetting
