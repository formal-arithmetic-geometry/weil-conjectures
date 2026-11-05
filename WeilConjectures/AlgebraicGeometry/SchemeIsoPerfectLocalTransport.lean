/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import all WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import all WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedRestrictionSquare

@[expose] public section

universe u w₁ w₂

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
