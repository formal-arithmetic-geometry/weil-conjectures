/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactProjectionFormula
import all WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleOrigin
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite site comparison of counits, projections and transposes

Source: blueprint main-20261015, lem-pur-co-smooth-etale-locality, Steps 1 and 3;
Stacks Project, Tags 0B65, 07A4, 0GL1 and 0F7F
(blueprint: lem-pur-finite-site-counit-projection-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

attribute [local instance 2000] isNoetherian_of_finite
attribute [local irreducible] Etale.derivedTensor derivedTensor
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso
  Etale.projectionMapOfCompactification projectionMapOfCompactification
  Etale.rightDerivedLowerStarProjectionMap rightDerivedLowerStarProjectionMap
  Etale.derivedOpenImmersionLowerShriekProjectionIso derivedOpenImmersionLowerShriekProjectionIso
  compactSupportSiteComparison

attribute [local semireducible] Etale.derivedTensor derivedTensor
  Etale.projectionMapOfCompactification projectionMapOfCompactification
  Etale.rightDerivedLowerStarProjectionMap rightDerivedLowerStarProjectionMap
  Etale.derivedOpenImmersionLowerShriekProjectionIso derivedOpenImmersionLowerShriekProjectionIso
  compactSupportSiteComparison

attribute [local irreducible] derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
  comparisonOpenTensorIso comparisonOpenDerivedPullbackIso

local syntax (name := startTensorProof) "start_tensor_proof" : tactic
local syntax (name := finishTensorProof) "finish_tensor_proof" : tactic

open Lean Meta Elab Tactic in
open Lean Meta Elab Tactic in
end AlgebraicGeometry.ProEtale
