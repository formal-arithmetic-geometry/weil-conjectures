/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift
import WeilConjectures.AlgebraicGeometry.AffinePerfectPlusLocallyFree
import WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Triangulated

/-! # Affine perfect extension after adjoining a shift

Source: literature/stacks-project/perfect.tex, Tag 08EI (Lemma 36.13.8)
(blueprint: lem-sc-affine-perfect-plus-shift).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

-- Cone cancellation for the projection onto the first summand.

end AlgebraicGeometry
