/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSiteBasic
import WeilConjectures.CategoryTheory.InternalActionSite.TwistedModulePresheafEquivalence
import WeilConjectures.CategoryTheory.InternalActionSite.EquivariantModuleSheafificationReflector
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

/-!
# Internal action site presentation

Source: the action-site construction, Stacks 00VH, 00WJ, 00YR, 03CY and 03DA
(blueprint: lem-sfb-internal-action-site-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C] (K : Cᵒᵖ ⥤ GrpCat.{u})

end CategoryTheory.InternalActionSite
