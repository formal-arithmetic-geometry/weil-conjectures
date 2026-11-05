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
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedAlgebraData
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedDegreeData
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedKernelSquareZero

/-! # Algebraic graded presentation of the tensor ideal sequences

Source: Stacks Project, Tag 09MS, coherent-equation-ses and its direct sum over degrees.
(blueprint: lem-sc-square-zero-tensor-graded-presentation).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] RingedSpace.moduleCohomology
  boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
noncomputable section

end
end AlgebraicGeometry.Scheme.Modules
