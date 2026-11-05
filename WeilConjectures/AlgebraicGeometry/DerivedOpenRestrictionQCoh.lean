/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Quasi-coherence and derived restriction

Source: Stacks Project, Tags 08DW and 06Z0; exact restriction to open subschemes.
(blueprint: lem-pc-derived-open-restriction-qcoh-iff).
-/

@[expose] public section

universe u w wO

open CategoryTheory CategoryTheory.Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry
