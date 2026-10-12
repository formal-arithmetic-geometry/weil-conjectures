/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Limits.Types.Images

/-!
# Mittag-Leffler towers of nonempty sets have nonempty limits

A tower `⋯ → E₂ → E₁ → E₀` of nonempty sets satisfying the Mittag-Leffler condition has a
nonempty inverse limit: restricted to the eventual images, the transition maps become surjective
(`CategoryTheory.Functor.surjective_toEventualRanges`), and a tower of surjections of nonempty
sets has a compatible sequence.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Functor

/-- **A Mittag-Leffler tower of nonempty sets has a nonempty limit.**
(blueprint: `lem-weil-pbc-ml-sets-tower-limit-nonempty`) -/
theorem nonempty_sections_of_isMittagLeffler (F : ℕᵒᵖ ⥤ Type u) [∀ n, Nonempty (F.obj n)]
    (hF : F.IsMittagLeffler) : F.sections.Nonempty := by
  let G := F.toEventualRanges
  have : Nonempty (G.obj ⟨0⟩) := F.toEventualRanges_nonempty hF _
  obtain ⟨x, -⟩ := Types.surjective_π_app_zero_of_surjective_map_aux
    (fun n ↦ F.surjective_toEventualRanges hF _) (Classical.arbitrary (G.obj ⟨0⟩))
  exact ⟨_, (F.toEventualRangesSectionsEquiv x).2⟩

end CategoryTheory.Functor
