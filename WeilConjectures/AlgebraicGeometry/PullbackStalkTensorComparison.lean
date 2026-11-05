/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Stalk tensor coordinates for a scheme pullback comparison

Source: Stacks Project, Tag 08IB, local affine tensor comparison, and Tag 0098,
stalks of module pullback (blueprint: def-pc-pullback-stalk-tensor-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.PullbackStalkTensor

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)

attribute [local instance] leftAlgebra rightAlgebra

attribute [local instance] stalkAlgebra

attribute [local instance] tensorAlgebra

end AlgebraicGeometry.PullbackStalkTensor

end
