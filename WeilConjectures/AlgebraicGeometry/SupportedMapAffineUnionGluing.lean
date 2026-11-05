/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.SupportedAffineOverlapMap
import WeilConjectures.AlgebraicGeometry.SupportedRelativeOpenGluing
import WeilConjectures.AlgebraicGeometry.OpenDerivedLocalizationData

/-! # Supported perfect gluing on the union with an affine open

Source: Stacks Project, Tag 09IM, two-open construction before ambient extension.
(blueprint: lem-sc-supported-map-affine-union-gluing).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
