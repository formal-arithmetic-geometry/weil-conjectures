/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnit
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomRestrictionSurjective
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomRestrictionEventuallyZero
import Mathlib.CategoryTheory.Limits.Types.Filtered

@[expose] public section
universe uMain wMain
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry
