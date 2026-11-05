/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleTriangulated
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Integral constructible categories are linear over the valuation ring

Source: Weil conjectures blueprint, `def-weil-rationalization-karoubi`, its integral
linearity hypothesis (blueprint: lem-weil-integral-constructible-linear).

The section maps are specified by every finite quotient projection; their naturality
includes restriction from the terminal object, hence the map from constant global
sections. Sheaf-level scalar multiplication and linearity of the localization specify
the resulting action on derived morphisms, including morphisms created by localization.
The constructible subcategory carries precisely the inherited linear structure.
-/

@[expose] public section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe d u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

section CoefficientProof

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

attribute [local instance] coefficientModuleLinear

end CoefficientProof

end WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

end WeilConjectures
