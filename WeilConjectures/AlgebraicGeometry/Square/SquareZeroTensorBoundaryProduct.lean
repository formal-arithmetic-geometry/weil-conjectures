/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.Boundary.BoundaryDerivationSquareZero
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorBoundaryGradedRealization

/-! # The two-section product identity for transported tensor boundaries

Source: Stacks Project, Tags 09MS and 0B8S.
(blueprint: lem-sc-square-zero-tensor-boundary-product).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u wC wD
attribute [local irreducible] RingedSpace.moduleCohomology
  RingedSpace.moduleSectionBoundary boundaryCoefficientCohomologyIso
  canonicalTensorBoundaryComparisons
noncomputable section

end
end AlgebraicGeometry.Scheme.Modules
