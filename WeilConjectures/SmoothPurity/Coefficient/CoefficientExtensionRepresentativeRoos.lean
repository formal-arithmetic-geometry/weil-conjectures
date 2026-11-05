/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoosComparisonSupplement
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRestrictedTower
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Roos comparison of strict coefficient-extension representatives

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction constantSheaf HasDerivedCategory.standard
  SemilinearSections.hasDerived coefficientExtensionSystem

variable (A : CoefficientExtensionSystems l E L ι W)

attribute [local irreducible] towerRoosComparison

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] scalarRoosComparison integralScalarComplexFunctor

attribute [local irreducible] coefficientSequenceProjection
  coefficientRestrictedEvaluationIso coefficientConstantTowerProjection
  coefficientConstantTowerLimit coefficientSequenceRestriction

end WeilConjectures
