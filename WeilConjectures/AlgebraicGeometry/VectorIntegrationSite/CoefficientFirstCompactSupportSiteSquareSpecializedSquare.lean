/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorSiteEquations
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.CoefficientFirstCompactSupportSiteSquareCoefficient

/-! # Specialization of the coefficient-first compact-support comparison to a vector bundle. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] Scheme.Modules
  Etale.vectorBundlePurityLower Etale.vectorBundlePurityCompactification
  Etale.vectorIntegrationSource
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
end AlgebraicGeometry.ProEtale.VectorIntegrationSite
