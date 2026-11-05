/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear

import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import all WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear

/-! # Constant-scalar linearity of the normalized integral pullback

Source: the rational paragraph of `def-weil-derived-pullback-tensor-hom`;
Bhatt--Scholze, Lemma 6.5.9(4), and Stacks Tag 099N(5).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

open CategoryTheory.Limits Opposite

section Representatives

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] coefficientModuleLinear

section RoosLinearity

variable {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
open CochainComplex

end RoosLinearity

end Representatives

end WeilConjectures
