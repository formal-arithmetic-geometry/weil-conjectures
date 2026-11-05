/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionInflation
public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSitePresentation
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # Normalized fixed-subsheaf adjunctions for a product of group sheaves

Source: main-20261015, direct-image stability paragraph (3), agent-formulated
fixed-subsheaf input; Stacks Tags 03CV, 00VH, 00VM, 0037, 0DV0
(blueprint: lem-sfb-sheaf-product-fixed-adjunction).

The action categories and their sectionwise additive structures are the existing
`InternalActionSite.EquivariantSheaf` categories, recorded by the definition node
`def-sfb-equivariant-module-sheaves`. The specifications below identify
invariants by their injective inclusions and exact fixed-section images. No invariant
object or comparison is chosen from an unspecified existence assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

end CategoryTheory.InternalActionSite
