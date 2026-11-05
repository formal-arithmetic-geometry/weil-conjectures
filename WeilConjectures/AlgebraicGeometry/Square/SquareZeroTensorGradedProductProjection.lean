/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedPresentation
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedQuotientMultiply
import WeilConjectures.AlgebraicGeometry.SquareZeroTensorSectionProductComparison

/-! # Homogeneous sections and their product in a graded presentation

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-product-projection).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] RingedSpace.moduleCohomology
  boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
noncomputable section

attribute [irreducible] tensorGradedCoefficientProjection

end
end AlgebraicGeometry.Scheme.Modules
