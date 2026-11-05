/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryQuotientModel
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorDescent
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionPresentation

/-! # Strict tensor normalization of reduction from the ordinary quotient model

Source: Stacks 06YS, 06YY, 07A4 and 0941.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  CoefficientClosedStructure.tensor coefficientTotalTensor
  coefficientIntegralTensorModelIso coefficientSystemTensorModelIso
  coefficientScalarTensorIso coefficientEvaluationTensorIso

end WeilConjectures.OrdinaryQuotient
