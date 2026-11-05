/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedAlgebraData
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedDegreeData
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Local ideal coefficients of the graded quotient kernel

Source: Stacks Project, Tag 09MS, the direct-sum ideal sequence.
(blueprint: lem-sc-tensor-graded-kernel-local-ideal).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section
attribute [local instance] presheafMonoidalCategory presheafSymmetricCategory
  sheafificationMonoidal sheafificationBraided forgetToPresheafOfModulesLaxMonoidal

section KernelFactor
attribute [local irreducible] tensorGradedAlgebraMap tensorGradedUnit
  commAlgebraSheafModule tensorPullback

end KernelFactor

end
end AlgebraicGeometry.Scheme.Modules
