/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.SupportedMapInitialAmbientLift
import WeilConjectures.AlgebraicGeometry.SupportedMapAffineAttachment

/-! # The finite stabilization construction for supported map lifting

Source: Stacks Project, Tag 09IM, proof of Lemma 36.13.11.
(blueprint: lem-sc-perfect-supported-stabilized-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
