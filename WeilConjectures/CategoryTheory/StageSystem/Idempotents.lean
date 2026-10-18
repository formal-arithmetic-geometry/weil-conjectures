/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import WeilConjectures.CategoryTheory.StageSystem.Basic

/-!
# Idempotent completeness of the pair category of a stage system

If every stage `C i` of a stage system `S` over a directed preorder is idempotent complete, so is
its pair category `S.PairCategory`, the filtered `2`-colimit of the stages: an idempotent of the
pair category is represented at some stage `n`, is an idempotent after transport to a further
stage `p`, splits there, and the splitting maps to the pair category by the stage inclusion
`S.ι p`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category

namespace StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] (S : StageSystem C)

open PairCategory

/-- The pair category of a stage system whose stages are idempotent complete is idempotent
complete. -/
theorem isIdempotentComplete_pairCategory [∀ i, IsIdempotentComplete (C i)] :
    IsIdempotentComplete S.PairCategory := by
  refine ⟨fun X e he ↦ ?_⟩
  revert he
  induction e using hom_induction with
  | h n hX hY u =>
    intro he
    rw [mkHom_comp_mkHom, mkHom_eq_mkHom_iff'] at he
    obtain ⟨p, h, h', hp⟩ := he
    rw [tr_comp] at hp
    obtain ⟨Y, i, r, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split
      (X.toStage (hX.trans h)) (S.tr h u) hp
    refine ⟨(S.ι p).obj Y, (S.ι p).map i ≫ (S.isoToStage X (hX.trans h)).inv,
      (S.isoToStage X (hX.trans h)).hom ≫ (S.ι p).map r, ?_, ?_⟩
    · simp [← Functor.map_comp, h₁]
    · rw [← mkHom_tr h u, mkHom_eq_isoToStage]
      simp [← Functor.map_comp_assoc, h₂]

end StageSystem

end CategoryTheory
