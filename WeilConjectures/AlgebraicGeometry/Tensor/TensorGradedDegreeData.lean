/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedAlgebraData
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitEpi

/-! # Exactness and degree projections for a graded quotient

Source: Stacks Project, Tag 09MS, direct sum of coherent-equation-ses.
(blueprint: lem-sc-tensor-graded-degree-data).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section
attribute [local irreducible] tensorGradedAlgebraMap tensorGradedUnit
  commAlgebraSheafModule tensorPullback

end
end AlgebraicGeometry.Scheme.Modules
