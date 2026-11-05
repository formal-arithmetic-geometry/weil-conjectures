/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FlatRingedDiagramInput.FlatRingedDiagramRestrictionDefs
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Ordinary coefficient comparison isomorphisms

Source: Stacks Project, Modules on Sites, Tag 03D3.
(blueprint: lem-weil-pbc-flat-restriction-ordinary-comparisons).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.FlatRingedDiagramInput

open MonoidalCategory
open CartesianMonoidalCategory

section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}
  (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]

end

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}
  (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]

-- Restriction preserves the underlying sheaf but changes its bundled scalar action.
end CategoryTheory.FlatRingedDiagramInput
