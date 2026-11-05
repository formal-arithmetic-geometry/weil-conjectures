/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Common.CommonStageInternalHomData
import all WeilConjectures.SmoothPurity.CommonStageInternalHom.CommonStageInternalHomCoherenceLemmas

/-! The missing normalized Hom comparison coherence for common-stage transport.
Source: the common-stage internal-Hom paragraph of def-weil-derived-pullback-tensor-hom.
(blueprint: lem-weil-common-stage-internal-hom-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.auxLemma false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open Opposite CategoryTheory AlgebraicGeometry

namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  rationalDerivedInternalHom sfRationalScalarExtension ScalarLocalization.category
  StageSystem.PairCategory.mkHom
  commonStageHomComparison rationalHomScalarComparison operationStageTransitionIso
  scalarAssociator GeneralAlgebraicallyClosedCoefficients.associator
  sfRationalScalarComp sfRationalScalarUnit
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue ScalarLocalization.composition
  sfIntegralConstructible ScalarLocalization.linear ScalarLocalization.preadditive
  Linear.homModule Preadditive.homGroup Preadditive.fullSubcategory
  Linear.fullSubcategory sfIntegralConstructibleLinear

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

set_option allowUnsafeReducibility true in
attribute [local reducible] ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  commonStageHomObject commonStageHomPairAtStage rationalHomScalarPair

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (W : Scheme.{u})

namespace CommonStageInternalHom

attribute [local irreducible] rawComparison
set_option allowUnsafeReducibility true in
attribute [local reducible] scalarPairs

variable (P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
  (L : Index l Ω)
  (h : (commonStageHomObject l Ω W P).stage ≤ L)
  (h' : (commonStageHomObject l Ω W Q).stage ≤ L)
  (a : (commonStageHomPairAtStage l Ω W Q L h').obj.1.unop ⟶
    (commonStageHomPairAtStage l Ω W P L h).obj.1.unop)
  (b : (commonStageHomPairAtStage l Ω W P L h).obj.2 ⟶
    (commonStageHomPairAtStage l Ω W Q L h').obj.2)

attribute [local irreducible] inputStep pairStep

end CommonStageInternalHom
end WeilConjectures
