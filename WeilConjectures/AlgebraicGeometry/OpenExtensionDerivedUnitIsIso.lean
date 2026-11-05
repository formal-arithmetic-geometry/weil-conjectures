/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitIsIso
import WeilConjectures.Algebra.Homology.DerivedOpenShriekAdjunction
import Mathlib.CategoryTheory.Monad.Adjunction

/-! # Invertibility of the transported derived open extension unit
Source: Stacks Project, Tags 00A7, 08BS and 06YB.
(blueprint: lem-pc-open-extension-derived-unit-isiso). -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
  TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

noncomputable section
universe u w

end
end AlgebraicGeometry
