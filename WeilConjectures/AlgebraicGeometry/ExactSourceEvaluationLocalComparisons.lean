/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.CanonicalEvaluationOpenRestriction
import WeilConjectures.AlgebraicGeometry.ExactSourceEvaluationOpenModels

/-! # The local representative equation for evaluation with an exact Hom source

Source: Stacks Project, Tags 08DL, 08DM and 08DQ, the ordinary complex models;
Tag 08DJ, the tensor-Hom representative equation.
(blueprint: lem-pc-exact-source-evaluation-local-comparisons).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

end AlgebraicGeometry
