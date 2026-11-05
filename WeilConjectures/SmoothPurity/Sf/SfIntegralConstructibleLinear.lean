/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Constant-section linearity of the intrinsic integral constructible category

Source: Weil blueprint, `def-weil-rationalization-karoubi`, order 1460, the integral
linearity prerequisite (blueprint: lem-weil-integral-constructible-linear).

The ambient constant-section action is the published `integralCoefficientLinear`.
The full subcategory here is the currently recorded `sfIntegralConstructibleCategory`,
with the triangulation of `SfIntegralConstructibleTriangulated`. Legacy declarations
remain available through the public import.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{u})

end WeilConjectures
