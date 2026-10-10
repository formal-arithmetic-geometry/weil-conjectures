/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Finiteness

/-!
# Images of finitely generated subgroups

The image of a finitely generated subgroup under a group homomorphism is finitely generated.
-/

@[expose] public section

/-- The image of a finitely generated subgroup is finitely generated. -/
@[to_additive /-- The image of a finitely generated additive subgroup is finitely generated. -/]
theorem Subgroup.FG.map {G G' : Type*} [Group G] [Group G'] {P : Subgroup G} (h : P.FG)
    (e : G →* G') : (P.map e).FG := by
  classical
  obtain ⟨S, rfl⟩ := h
  exact ⟨S.image e, by rw [Finset.coe_image, MonoidHom.map_closure]⟩
