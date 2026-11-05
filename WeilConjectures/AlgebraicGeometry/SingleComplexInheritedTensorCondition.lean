/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
import WeilConjectures.AlgebraicGeometry.TensorStalkComparisonSquares
import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonInheritance

/-! # Tensor inheritance of the single-complex base-change condition

Source: Stacks Project, perfect.tex, Tag 0DJA, part (1)
(blueprint: lem-pc-rf-single-complex-inherited-tensor-condition).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false

end AlgebraicGeometry
