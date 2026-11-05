/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
public import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearStageTowerTransport
import WeilConjectures.SmoothPurity.Rational.RationalTensorTowerCoherence

/-! # Coherence of the rational tensor scalar comparisons

Source: the common-stage tensor argument of def-weil-derived-pullback-tensor-hom,
using the normalized scalar-extension comparisons of
lem-pur-integral-operations-scalar-extension; Stacks Project, Tags 07A4 and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w u₁ v₁ u₂ v₂
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] rationalDerivedTensor sfRationalScalarExtension
  rationalTensorScalarComparison HasDerivedCategory.standard integralCoefficientLinear
  ObjectProperty.FullSubcategory.category

section ProofHelpers

section
variable (l : ℕ) [Fact l.Prime]
  (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] scalarAssociator

end
end ProofHelpers

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

attribute [local irreducible] scalarAssociator

end WeilConjectures
