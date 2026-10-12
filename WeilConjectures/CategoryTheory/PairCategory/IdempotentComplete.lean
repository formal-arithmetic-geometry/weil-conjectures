/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.PairCategory.Basic
public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness of the pair category

If every stage of a directed system of categories is idempotent complete, then so is its pair
category `PairCategory F`: an idempotent of `(i, A)` is represented by an idempotent at some
stage `k`, which splits there, and the splitting is carried to the pair category by the stage
inclusion `j_k`. Consequently the inclusion of the pair category into its Karoubi envelope is
an equivalence, so no Karoubi envelope has to be taken (blueprint `def-weil-pbc-qbar-category`).

The Karoubi envelope of blueprint `def-weil-karoubi-envelope` is Mathlib's
`CategoryTheory.Idempotents.Karoubi`, with inclusion `CategoryTheory.Idempotents.toKaroubi`;
the additive categories of blueprint `def-weil-additive-category` are the preadditive
categories with `CategoryTheory.Limits.HasFiniteBiproducts`.

## Main results

- `CategoryTheory.PairCategory.isIdempotentComplete` : the pair category is idempotent complete
  when the stages are.
- `CategoryTheory.PairCategory.toKaroubi_isEquivalence` : the inclusion into the Karoubi envelope
  is an equivalence.
-/

@[expose] public section

universe w v u

open CategoryTheory Category Idempotents Pseudofunctor

namespace CategoryTheory.PairCategory

variable {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)]
  {F : Pseudofunctor (LocallyDiscrete ι) Cat.{v, u}}

/-- The pair category of a directed system of idempotent complete categories is idempotent
complete. -/
instance isIdempotentComplete [∀ i : ι, IsIdempotentComplete (F.obj ⟨i⟩)] :
    IsIdempotentComplete (PairCategory F) := by
  refine ⟨fun X p hp ↦ ?_⟩
  obtain ⟨k, hX, hX', u, rfl⟩ := exists_rep p
  rw [homMk_comp_homMk, homMk_eq_homMk_iff] at hp
  obtain ⟨k', h, e⟩ := hp
  rw [trHom_comp] at e
  rw [← homMk_trHom h hX hX' (hX.trans h) (hX.trans h) u]
  obtain ⟨Y, i, r, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split _ _ e
  refine ⟨(incl F k').obj Y, (incl F k').map i ≫ (isoToStage X (hX.trans h)).inv,
    (isoToStage X (hX.trans h)).hom ≫ (incl F k').map r, ?_, ?_⟩
  · rw [assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, h₁, Functor.map_id]
  · rw [assoc, ← Functor.map_comp_assoc, h₂, homMk_eq]

/-- Blueprint `def-weil-karoubi-envelope`: the inclusion `K ↦ (K, 𝟙)` of the pair category of a
directed system of idempotent complete categories into its Karoubi envelope
`CategoryTheory.Idempotents.Karoubi` is an equivalence. -/
lemma toKaroubi_isEquivalence [∀ i : ι, IsIdempotentComplete (F.obj ⟨i⟩)] :
    (toKaroubi (PairCategory F)).IsEquivalence :=
  inferInstance

end CategoryTheory.PairCategory
