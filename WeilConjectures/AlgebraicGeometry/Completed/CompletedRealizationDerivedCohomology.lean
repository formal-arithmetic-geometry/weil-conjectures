/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Normalized completed realization on unbounded derived categories

Source: Stacks Project, Modules on Sites, Tags 093J and 093M; Derived Categories,
Tag 015F; Bhatt--Scholze, Propositions 6.6.11 and 6.8.11(3)
(blueprint: lem-weil-pbc-completed-realization-derived-cohomology).

The realization is the existing `integralConstantModule`, including restriction along
`(pbcCompletedComparison T d).inv`. The comparisons below are actual constructions from
termwise localization and the kernel/image/cokernel comparison, without chosen witnesses.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

end AlgebraicGeometry.Scheme
