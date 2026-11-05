/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedPresentation
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial

/-! # Transport of maps between square-zero tensor kernels

Source: Stacks Project, Tags 09MS, 01XC and 01F8.
(blueprint: lem-sc-tensor-boundary-kernel-map-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] RingedSpace.moduleCohomology
  moduleCohomologyEdgeMap moduleCohomologyFMap
  boundaryIdealKernelIso boundaryCoefficientDegreeIso
noncomputable section

attribute [irreducible] tensorBoundaryKernelPushforwardIso tensorBoundaryKernelMap

attribute [local irreducible] boundaryCoefficientCohomologyIso

end
end AlgebraicGeometry.Scheme.Modules
