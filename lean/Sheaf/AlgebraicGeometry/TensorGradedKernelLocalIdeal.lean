/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.TensorGradedAlgebraData

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
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section
attribute [local irreducible] tensorGradedAlgebraMap tensorGradedUnit
  commAlgebraSheafModule tensorPullback

/-- Two sections of the graded quotient kernel locally lie in the extended base ideal.
No square-zero assumption, multiplication law, or invertibility assumption is used.
Source: Stacks Project, Tag 09MS, direct-sum ideal sequence, and Tag 04CJ (1).
Proof: apply the closed-immersion unit quotient formula in every degree and take
its sheaf direct sum. Exactness of sheaf coproducts and the two coproduct universal
properties in A identify ker p with the direct sum of J L^d. On stalks, each of the
two given kernel germs is a finite sum of terms r times b_d(s), with r in J_x.
Represent these finitely many module germs and ideal germs on a common neighborhood,
and shrink to make their finite-sum presentations hold as section equalities.
Restrict to an affine neighborhood V of x contained in that neighborhood and U.
The ideal germs can be represented by sections of J.toModules; their images on V
lie in J.ideal V by range_toModulesι_app. Linearity of b_d over the structure sheaf
identifies each summand with the image of r under the structure map of B times
b_d(s), hence with an element of the mapped ideal. Its closure under finite sums
proves the two memberships. Intersecting the finitely many neighborhoods gives
one V for both sections. This is a statement about local ideal generation, valid
for arbitrary L and arbitrary j.ker; neither J^2 = 0 nor homogeneous multiplication
is needed. The argument is vacuous on the empty scheme.
(blueprint: lem-sc-tensor-graded-kernel-local-ideal). -/
theorem tensorGradedKernel_locally_ideal {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) (A : TensorGradedAlgebraData j L)
    (U : X.Opens) (a b : A.B.right.obj.obj (op U))
    (ha : A.p.right.hom.app (op U) a = 0)
    (hb : A.p.right.hom.app (op U) b = 0) (x : X) (hx : x ∈ U) :
    ∃ (V : X.affineOpens) (hVU : V.1 ≤ U), x ∈ V.1 ∧
      A.B.right.obj.map (homOfLE hVU).op a ∈
        Ideal.map (A.B.hom.hom.app (op V.1)).hom (j.ker.ideal V) ∧
      A.B.right.obj.map (homOfLE hVU).op b ∈
        Ideal.map (A.B.hom.hom.app (op V.1)).hom (j.ker.ideal V) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
