/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictScalarCompletionFunctorComparison
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictIntegralCompletionPresentation
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionLimits
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionFiniteConstantModels
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionScalarPresentation
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictIntegralScalarPullback
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionPrincipalQuotientModels

/-! # Strict completion under section action and pro-etale restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open WeilConjectures
open CategoryTheory.InternalAbelianSheafModule

-- Upstream's `HasDerivedCategory` instances on these module categories are found first and then
-- fail the final defeq check, which blocks `HasDerivedCategory.ofIsGrothendieckAbelian`.
attribute [-instance] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOverModules

namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
