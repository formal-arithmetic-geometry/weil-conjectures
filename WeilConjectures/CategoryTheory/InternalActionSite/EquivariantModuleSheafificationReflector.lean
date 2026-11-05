/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSiteBasic
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Equivariant module sheafification as a reflector

Source: Stacks Project, Modules on Sites, Tag 03CY, and Sites, Tags 00WH, 00WJ,
00YR; the agent-formulated internal-action extension supporting paragraph (3) of
main-20261015, sk-thm-sf-ctf-stability-direct-images
(blueprint: lem-sfb-equivariant-module-sheafification-reflector).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InternalActionSite

section ActionConstruction

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : Cᵒᵖ ⥤ GrpCat.{u}) (R : Sheaf J RingCat.{u})
  (P : EquivariantPresheaf K R.obj)

end ActionConstruction

end CategoryTheory.InternalActionSite
