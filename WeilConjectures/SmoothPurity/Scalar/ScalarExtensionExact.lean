/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
public import WeilConjectures.SmoothPurity.Supporting.RationalizationKaroubi
public import WeilConjectures.CategoryTheory.ScalarLocalization.RationalizationLocalization
public import WeilConjectures.CategoryTheory.Shift.CommShiftExt
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Triangulated.Functor

import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

/-! # Exactness of finite scalar extension

Source: blueprint `sec-smooth-purity/sk-prop-sf-pf-reduction`, order 1883
(blueprint: lem-weil-scalar-extension-exact-triangulated).
The shift comparison is specified on integral representatives, including its sign.
-/

@[expose] public section
set_option autoImplicit false

universe d u
open CategoryTheory TensorProduct

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

attribute [local instance] integralConstructibleShift_linear

attribute [instance] rationalConstructibleScalar_exact

end WeilConjectures
