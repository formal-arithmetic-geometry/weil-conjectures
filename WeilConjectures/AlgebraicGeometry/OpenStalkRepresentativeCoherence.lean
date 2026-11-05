/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenDerivedAdditiveStalkIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Representative coherence for exact open stalk restriction

Source: Stacks Project, Tags 0098, 08DW and 015F; exact localization factorization.
(blueprint: lem-pc-open-stalk-representative-coherence).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
open SingleComplexBaseChange

-- Abstract functors keep localization calculations from unfolding the stalk construction.

-- Homology of the preceding localization identity, with both forgetful comparisons.

end AlgebraicGeometry
