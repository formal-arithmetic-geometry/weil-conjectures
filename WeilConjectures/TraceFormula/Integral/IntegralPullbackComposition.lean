/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
import WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence
import WeilConjectures.PoincareDuality.Integral.IntegralSystemPullbackLiftAssociativity

/-!
# Composition of completed integral derived pullbacks

Source: Stacks Project, Tags 099N(2),(5) and 0D6D; Bhatt--Scholze,
Lemmas 3.5.5 and 3.5.7
(blueprint: lem-pod-integral-pullback-composition).

All categories use modules over the completed integral coefficient sheaf. The
positive exponent is n+1. The reduction comparison is the actual projection-adjoint
map, expressed in the published finite ring-sheaf presentation. Quantification over
all good representatives makes the reduction clause independent of choices.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option allowUnsafeReducibility true in
attribute [local irreducible] finiteSystemDerivedPullback finiteSystemDerivedEvaluation
  integralSystemReduction integralSystemReductionEvaluation
  finiteSystemDerivedComposition finiteSystemDerivedPullbackEvaluation
  constructibleIntegralPullback integralDerivedPullback
  integralFiniteCanonicalPullbackComposition proEtaleConstantRingPullbackComposition
  integralSystemPullbackReductionIso integralPullbackReductionIso
  AlgebraicGeometry.Scheme.residueField
  completedIntegralCoefficientSheafUnrestricted
  proEtaleConstantRingDerivedPullback scalarReductionDerivedExtension

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
-- The natural isomorphisms compare two presentations of derived coefficient systems.

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end WeilConjectures
