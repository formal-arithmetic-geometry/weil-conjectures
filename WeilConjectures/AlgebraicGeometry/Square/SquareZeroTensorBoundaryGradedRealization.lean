/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedActionProjection
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedBoundaryProjection

/-! # Homogeneous realization of tensor boundaries

Source: Stacks Project, Tag 09MS, coherent-equation-ses and its direct sum over degrees;
Tag 0B8S, the quotient action on the square-zero kernel.
(blueprint: lem-sc-square-zero-tensor-boundary-graded-realization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
attribute [local irreducible] AlgebraicGeometry.Scheme.Modules.tensorPullback
  Functor.rightDerived Functor.rightDerivedToHomotopyCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u wC wD
attribute [local irreducible] RingedSpace.moduleSectionBoundary boundaryCoefficientCohomologyIso
  canonicalTensorBoundaryComparisons tensorGradedSection
noncomputable section

section GradedProjectionHelpers
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] RingedSpace.moduleCohomology

end GradedProjectionHelpers

end
end AlgebraicGeometry.Scheme.Modules
