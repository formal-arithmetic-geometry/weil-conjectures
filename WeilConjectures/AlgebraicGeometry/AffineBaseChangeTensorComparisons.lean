/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde

/-! # Tensor coordinates for the two sides of affine base change

Source: Stacks Project, Schemes, Lemma 01I9 and Cohomology of Schemes, Lemma 02KG.
(blueprint: lem-weil-pbc-affine-base-change-tensor-comparisons).
-/

@[expose] public section

universe u
open CategoryTheory Opposite TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end
end AlgebraicGeometry.Scheme.Modules
