/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.Algebra.Homology.OpenExtensionRestrictionIso
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monad.Adjunction

/-! # Derived open restriction is a localization
Source: Stacks Project, Tags 08FE and 08BS.
(blueprint: lem-pc-derived-open-restriction-is-localization).
-/

@[expose] public section

universe u w wO
open CategoryTheory CategoryTheory.Limits
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry
