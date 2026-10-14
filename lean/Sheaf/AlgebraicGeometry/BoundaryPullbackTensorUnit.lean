/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons

/-! # Section normalization of the boundary pullback tensor comparison

Source: Stacks Project, Tag 01CD.
(blueprint: lem-sc-boundary-pullback-tensor-unit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- The tensor comparison induced by uniqueness of left adjoints preserves unit sections.
Source: Stacks Project, Tag 01CD, pullback of tensor products; Tag 0096, adjunction.
(blueprint: lem-sc-boundary-pullback-tensor-unit).
Proof: Write boundaryPullbackComparison as the unique comparison with Mathlib pullback.
The unit-leftAdjointUniq equation identifies the chosen tensor-pullback unit followed
by the comparison with the Mathlib pullback unit. The monoidal pullback tensorator
sends that unit on a pure tensor to the tensor of the two unit sections: this follows
from its construction by the bilinear map on sections and the sheafification unit.
Expand boundaryPullbackTensorIso, apply these three unit comparison equations, and
cancel the inverse comparison on each factor. This proves the equality on each open
without any invertibility, closed immersion or square-zero assumption. The formula
also holds on the empty open and for zero modules by the same linear identities. -/
theorem boundaryPullbackTensorIso_unit_tmul {X Z : Scheme.{u}} (j : Z ⟶ X)
    (M N : X.Modules) (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (boundaryPullbackTensorIso j M N).hom.app (j ⁻¹ᵁ U)
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app (M ⊗ N)).app U
          (tmulSection s t)) =
      tmulSection (M := (tensorPullback j).obj M) (N := (tensorPullback j).obj N)
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app M).app U s)
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app N).app U t) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
