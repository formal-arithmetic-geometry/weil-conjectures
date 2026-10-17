/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic
public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness of the pair category

If every stage of a stage system is idempotent complete, then so is its pair category: an
idempotent of `(i, x)` is represented by an idempotent at some stage `k`, which splits there,
and the splitting is carried to the pair category by the stage inclusion `j_k`. Consequently
the inclusion of the pair category into its Karoubi envelope is an equivalence, so no Karoubi
envelope has to be taken (blueprint `def-weil-pbc-qbar-category`).

The Karoubi envelope of blueprint `def-weil-karoubi-envelope` is Mathlib's
`CategoryTheory.Idempotents.Karoubi`, with the inclusion `CategoryTheory.Idempotents.toKaroubi`.

## Main results

- `CategoryTheory.StageSystem.PairCategory.isIdempotentComplete`: the pair category is
  idempotent complete when the stages are.
- `CategoryTheory.StageSystem.PairCategory.isEquivalence_toKaroubi`: the inclusion into the
  Karoubi envelope is an equivalence.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Idempotents

namespace StageSystem.PairCategory

variable {I : Type w} [Preorder I] [IsDirectedOrder I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] {S : StageSystem C}

/-- The pair category of a stage system of idempotent complete categories is idempotent
complete. -/
instance isIdempotentComplete [∀ i, IsIdempotentComplete (C i)] :
    IsIdempotentComplete S.PairCategory := by
  refine ⟨fun X p hp ↦ ?_⟩
  obtain ⟨n, -, hX, hX', u, rfl⟩ := exists_le_mkHom_eq p X.stage
  rw [mkHom_comp_mkHom, mkHom_eq_mkHom_iff] at hp
  obtain ⟨k, h, e⟩ := hp
  rw [← tr_injective, tr_comp] at e
  rw [← mkHom_tr h u]
  obtain ⟨Y, i, r, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split _ _ e
  refine ⟨(S.ι k).obj Y, (S.ι k).map i ≫ (S.isoToStage X (hX.trans h)).inv,
    (S.isoToStage X (hX.trans h)).hom ≫ (S.ι k).map r, ?_, ?_⟩
  · rw [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, h₁, Functor.map_id]
  · rw [Category.assoc, ← Functor.map_comp_assoc, h₂, mkHom_eq_isoToStage]

/-- Blueprint `def-weil-karoubi-envelope` (with `def-weil-pbc-qbar-category`): the inclusion
`K ↦ (K, 𝟙)` of the pair category of a stage system of idempotent complete categories into its
Karoubi envelope `CategoryTheory.Idempotents.Karoubi` is an equivalence. -/
lemma isEquivalence_toKaroubi [∀ i, IsIdempotentComplete (C i)] :
    (toKaroubi S.PairCategory).IsEquivalence :=
  inferInstance

end StageSystem.PairCategory

end CategoryTheory
