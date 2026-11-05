/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import Mathlib.CategoryTheory.Localization.LocallySmall

/-! # Comparison data for inverse image opens of a union

Source: Stacks Project, Tag 08BW; canonical restriction diagram.
(blueprint: lem-sc-open-union-restriction-comparison-data).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

noncomputable section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  Functor.additive_of_preserves_binary_products

attribute [local irreducible] Functor.mapDerivedCategory transportDerived

end

end AlgebraicGeometry.Scheme
