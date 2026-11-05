/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedAlgebraData
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedKernelLocalIdeal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Topology.Sheaves.CommRingCat

/-! # Square-zero kernel of the graded tensor quotient

Source: Stacks Project, Tag 09MS, the square-zero direct-sum ideal sequence.
(blueprint: lem-sc-tensor-graded-kernel-square-zero).
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
