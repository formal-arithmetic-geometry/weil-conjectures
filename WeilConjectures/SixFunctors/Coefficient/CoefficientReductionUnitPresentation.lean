/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus

/-! # Strict quotient-unit presentations for reduction representatives

Source: Stacks 06YS, 06YY, 07A6 and 0941. These predicates depend on the reduction
functor, its adjunction and finite comparisons, independently of the closed tensor data.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] DerivedCategory DerivedCategory.Q DerivedCategory.Qh
  _root_.instCategoryDerivedCategory HasDerivedCategory.standard
  SheafOfModules.instPreadditive HomologicalComplex.instPreadditive
  completedIntegralCoefficientSheafUnrestricted scalarReductionExtension
  coefficientFiniteReductionModel CoefficientComparisonEquation CoefficientTransitionEquation
  coefficientComplexCompositeTransformation
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] CoefficientStrictReductionUnitPresentation

end WeilConjectures
