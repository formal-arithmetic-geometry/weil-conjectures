/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSiteBasic
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Trivial actions, restriction of actions, and underlying exactness

Source: paragraph (3) of the direct-image stability proof, internal-action input.
The following declarations are extracted unchanged from the two action theorem modules.
(blueprint: def-sfb-internal-action-inflation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]
  {K L : Cᵒᵖ ⥤ GrpCat.{u}} {R : Cᵒᵖ ⥤ RingCat.{u}}

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

end CategoryTheory.InternalActionSite
