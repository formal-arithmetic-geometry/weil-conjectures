/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedProductProjection
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorBoundaryKernelMapNaturality
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedQuotientActionHomogeneous
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedActionKernelSecondDiagonal

/-! # Homogeneous quotient multiplication on degree kernels

Source: Stacks Project, Tags 09MS and 0B8S.
(blueprint: lem-sc-tensor-graded-action-kernel-second).
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

end
end AlgebraicGeometry.Scheme.Modules
