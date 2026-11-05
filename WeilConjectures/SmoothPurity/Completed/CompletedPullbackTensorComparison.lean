/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorConstruction
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality
import WeilConjectures.SmoothPurity.Supporting.Tensor.RestrictionTensorRepresentativeTransport
import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! # Common-stage pullback/tensor comparison

Source: Stacks 07A4, 0941 and the blueprint common-stage coefficient convention.
(blueprint: def-pur-completed-pullback-tensor-comparison)

The integral, rational and finite constructions are re-exported unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

section CoherentSystems
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end CoherentSystems

section CommonComparison
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory StageHom
  commonStagePullbackObject commonStageTensorObject
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5
attribute [local irreducible] ScalarLocalization.category
attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  sfRationalScalarExtension rationalPullbackScalarComparison rationalTensorScalarComparison
  commonStagePullbackComparison commonStageTensorComparison operationStageTransitionIso
  canonicalRationalPullbackTensor
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

end CommonComparison

end WeilConjectures
