/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.AmbientOpenGluingObject
import WeilConjectures.AlgebraicGeometry.OpenUnionHomGluing

/-! # Relative two-open gluing without local finiteness conditions

Source: Stacks Project, Tag 08DG, Lemma cohomology-lemma-glue.
(blueprint: lem-sc-relative-open-gluing).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
