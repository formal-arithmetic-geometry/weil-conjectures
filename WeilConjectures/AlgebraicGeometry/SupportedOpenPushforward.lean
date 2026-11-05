/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforwardPerfectComponent
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforwardLocalComparisons
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionIsIsoOpenCover

/-! # Perfect pushforward and canonical maps for supported open inclusions

Source: Stacks Project, Tags 08DP and 08DF
(blueprint: lem-pc-supported-open-pushforward).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
