/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.SmoothBaseChange.ActualCompletedReductionReconstruction
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedQuotientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulReductionRoosTriangle
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import all WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The normalized completion Roos triangle under coefficient transport

Source: Stacks Tags 099M, 099N and 06YY; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-pur-completed-coefficient-completion-roos-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

open Opposite
open IntegralCoefficientPresentation
attribute [local instance 30000] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
attribute [local irreducible] completedReductionEvaluation
  pbcActualCompletion pbcActualCompletionUnit
  scalarReductionExistence scalarReductionDerivedExistence scalarReductionDerivedExtension
  scalarReductionExtension scalarReductionCounit normalizedDVRResCompletedComp
  completedIntegralCoefficientSheafUnrestricted normalizedDVRKFlatComparison
  CategoryTheory.Limits.limit

attribute [local irreducible] Functor.mapDerivedCategory

attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

attribute [local irreducible] tensorRestrictionComp moduleRestrictionComp
  pbcDerivedScalarAdjunction reductionDerivedChange
  normalizedDVRQuotient integralCoefficientSheafTransition

end WeilConjectures
