/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.Irreducible

/-!
# Passing to a proper closed subset raises the dimension by at least one

## Main results

* `topologicalKrullDim_add_one_le`: if `X` is an irreducible topological space and `Z` is a
  proper irreducible closed subset of `X`, then `dim Z + 1 ≤ dim X`. Indeed a chain of
  irreducible closed subsets of `Z` is a chain of irreducible closed subsets of `X`, all of them
  contained in `Z` and hence strictly smaller than `X` itself, so appending `X` to it gives a
  chain of length one more.
* `topologicalKrullDim_eq_bot_iff`: a topological space has Krull dimension `⊥` exactly when it
  is empty.
* `topologicalKrullDim_add_one_le_of_forall_maximal`: the same statement for a closed subset `Z`
  of an arbitrary subset `S` of a topological space, the irreducibility of the ambient space
  being replaced by the assumption that no maximal irreducible subset of `S` is contained in
  `Z`, and `topologicalKrullDim_lt_of_forall_maximal`, its strict form when `S` is nonempty of
  finite dimension.
-/

@[expose] public section

open Order Set Set.Notation TopologicalSpace

/-- If `Z` is a proper irreducible closed subset of an irreducible topological space `X`, then
the Krull dimension of `Z` is at least one less than the Krull dimension of `X`. -/
theorem topologicalKrullDim_add_one_le {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    {Z : Set X} (hZc : IsClosed Z) (hZi : IsIrreducible Z) (hZ : Z ≠ Set.univ) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim X := by
  have hZne : Nonempty Z := hZi.nonempty.to_subtype
  have : Nonempty (IrreducibleCloseds Z) :=
    ⟨⟨closure {Classical.arbitrary Z}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have : Nonempty (IrreducibleCloseds X) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
  rw [topologicalKrullDim, topologicalKrullDim, krullDim_eq_iSup_length,
    krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add, ENat.iSup_add,
    WithBot.coe_le_coe, iSup_le_iff]
  intro l
  let top : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have key : ∀ W : IrreducibleCloseds Z,
      IrreducibleCloseds.map (Subtype.val) continuous_subtype_val W < top := by
    intro W
    have hsub : (IrreducibleCloseds.map (Subtype.val) continuous_subtype_val W : Set X) ⊆ Z := by
      rw [IrreducibleCloseds.coe_map]
      exact closure_minimal (by rintro _ ⟨⟨x, hx⟩, -, rfl⟩; exact hx) hZc
    refine lt_of_le_of_ne (Set.subset_univ _) fun h ↦ hZ (Set.eq_univ_of_univ_subset ?_)
    exact fun x hx ↦ hsub (h ▸ hx)
  refine le_trans ?_ (le_iSup _
    ((l.map _ (IrreducibleCloseds.map_strictMono_of_isInducing
      Topology.IsInducing.subtypeVal)).snoc top (key _)))
  simp

/-- The Krull dimension of a topological space is `⊥` exactly when the space is empty. -/
theorem topologicalKrullDim_eq_bot_iff {X : Type*} [TopologicalSpace X] :
    topologicalKrullDim X = ⊥ ↔ IsEmpty X := by
  rw [topologicalKrullDim, krullDim_eq_bot_iff]
  exact ⟨fun h ↦ ⟨fun x ↦ h.elim ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩,
    fun h ↦ ⟨fun Z ↦ h.elim Z.isIrreducible.nonempty.some⟩⟩

/-- Let `Z ⊆ S` be subsets of a topological space, with `Z` closed. If no maximal irreducible
subset of `S` is contained in `Z`, then `dim Z + 1 ≤ dim S`.

Indeed a chain of irreducible closed subsets of `Z` is a chain of irreducible closed subsets of
`S`; its largest member is contained in some irreducible component of `S`, which by hypothesis
is not contained in `Z` and is therefore strictly larger than every member of the chain. So
appending it to the chain gives a chain of length one more. -/
theorem topologicalKrullDim_add_one_le_of_forall_maximal {X : Type*} [TopologicalSpace X]
    {S Z : Set X} (hZS : Z ⊆ S) (hZ : IsClosed Z)
    (h : ∀ T, Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) T → ¬T ⊆ Z) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim S := by
  rcases Set.eq_empty_or_nonempty Z with rfl | hZne
  · rw [show topologicalKrullDim (∅ : Set X) = ⊥ from
      topologicalKrullDim_eq_bot_iff.2 inferInstance, WithBot.bot_add]
    exact bot_le
  have : Nonempty Z := hZne.to_subtype
  have : Nonempty (IrreducibleCloseds Z) :=
    ⟨⟨closure {Classical.arbitrary Z}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have : Nonempty S := (hZne.mono hZS).to_subtype
  have : Nonempty (IrreducibleCloseds S) :=
    ⟨⟨closure {Classical.arbitrary S}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hincl : Topology.IsInducing (Set.inclusion hZS) :=
    (Topology.IsEmbedding.inclusion hZS).isInducing
  rw [topologicalKrullDim, topologicalKrullDim, krullDim_eq_iSup_length,
    krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add, ENat.iSup_add,
    WithBot.coe_le_coe, iSup_le_iff]
  intro l
  set W : IrreducibleCloseds S :=
    IrreducibleCloseds.map (Set.inclusion hZS) hincl.continuous l.last with hWdef
  obtain ⟨T, hTmem, hTsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (W : Set S) W.isIrreducible
  have hWZ : (W : Set S) ⊆ S ↓∩ Z := by
    rw [hWdef, IrreducibleCloseds.coe_map]
    refine closure_minimal ?_ (hZ.preimage continuous_subtype_val)
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hTZ : ¬ ((T : Set S) ⊆ S ↓∩ Z) := fun hc ↦
    h _ (maximal_isIrreducible_image_val hTmem) (by rintro _ ⟨x, hx, rfl⟩; exact hc hx)
  have hlt : W < ⟨T, hTmem.1, isClosed_of_mem_irreducibleComponents T hTmem⟩ := by
    refine lt_of_le_of_ne hTsub fun heq ↦ hTZ ?_
    have hcoe : (W : Set S) = T := congrArg _ heq
    exact hcoe ▸ hWZ
  refine le_trans ?_ (le_iSup _
    ((l.map _ (IrreducibleCloseds.map_strictMono_of_isInducing hincl)).snoc _ hlt))
  simp

/-- Let `Z ⊆ S` be subsets of a topological space, with `Z` closed and `S` nonempty of finite
dimension. If no maximal irreducible subset of `S` is contained in `Z`, then `dim Z < dim S`. -/
theorem topologicalKrullDim_lt_of_forall_maximal {X : Type*} [TopologicalSpace X]
    {S Z : Set X} (hZS : Z ⊆ S) (hZ : IsClosed Z) (hS : S.Nonempty) {n : ℕ}
    (hn : topologicalKrullDim S ≤ n)
    (h : ∀ T, Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) T → ¬T ⊆ Z) :
    topologicalKrullDim Z < topologicalKrullDim S := by
  have hle := topologicalKrullDim_add_one_le_of_forall_maximal hZS hZ h
  have hSbot : topologicalKrullDim S ≠ ⊥ := by
    rw [Ne, topologicalKrullDim_eq_bot_iff, not_isEmpty_iff]
    exact hS.to_subtype
  rcases eq_or_ne (topologicalKrullDim Z) ⊥ with hb | hb
  · rw [hb]
    exact bot_lt_iff_ne_bot.2 hSbot
  have hZn : topologicalKrullDim Z ≤ (n : ℕ) :=
    ((Topology.IsEmbedding.inclusion hZS).isInducing.topologicalKrullDim_le).trans hn
  lift topologicalKrullDim Z to ℕ∞ using hb with d hd
  have hdn : d ≤ (n : ℕ∞) := by exact_mod_cast hZn
  lift d to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top n) hdn with j
  exact ENat.WithBot.add_one_le_iff.mp hle
