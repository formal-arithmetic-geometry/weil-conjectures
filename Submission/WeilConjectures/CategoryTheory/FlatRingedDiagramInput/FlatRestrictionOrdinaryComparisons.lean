/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.FlatRingedDiagramInput.FlatRingedDiagramRestrictionDefs
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Adjunction.Mates

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

private noncomputable abbrev base
    {T : Type u} [SmallCategory T] {τ : GrothendieckTopology T}
    (R : Sheaf τ CommRingCat.{u}) :=
  (sheafCompose τ (forget₂ CommRingCat RingCat)).obj R

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
