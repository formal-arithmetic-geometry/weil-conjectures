/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.SupportedMapAffineUnionGluing
import WeilConjectures.AlgebraicGeometry.SupportedMapInitialAmbientLift
import WeilConjectures.AlgebraicGeometry.OpenDerivedLocalizationData

/-! # One affine attachment for supported stabilized maps

Source: Stacks Project, Tag 09IM.
(blueprint: lem-sc-supported-map-affine-attachment).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
