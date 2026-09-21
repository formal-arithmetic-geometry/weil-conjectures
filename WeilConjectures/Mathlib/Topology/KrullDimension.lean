/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.Irreducible

/-!
# The Krull dimension of a subset, and of a proper closed subset

## Main results

* `topologicalKrullDim_eq_bot_iff`: a topological space has Krull dimension `⊥` exactly when it
  is empty.
* `topologicalKrullDim_univ`: `univ`, as a subspace, has the Krull dimension of the space.
* `topologicalKrullDim_add_one_le_of_forall_maximal`: if `Z ⊆ S` are subsets of a topological
  space with `Z` closed in `S`, and no maximal irreducible subset of `S` is contained in `Z`,
  then `dim Z + 1 ≤ dim S`. Indeed a chain of irreducible closed subsets of `Z` is a chain of
  irreducible closed subsets of `S`, and appending an irreducible component of `S` containing
  its largest member — which by hypothesis is not contained in `Z` — gives a chain of length one
  more. `topologicalKrullDim_lt_of_forall_maximal` is its strict form, when `S` is nonempty of
  finite dimension.
* `topologicalKrullDim_add_one_le`: the special case of an irreducible ambient space, where the
  hypothesis on `Z` reads `Z ≠ univ`.
* `topologicalKrullDim_le_of_subset`: the Krull dimension of a subset is monotone in the subset.
* `topologicalKrullDim_le_of_forall_maximal`: **the dimension of a subset is controlled by the
  dimensions of its maximal irreducible subsets.** A chain of irreducible closed subsets of `S`
  has its largest member inside some maximal irreducible subset of `S`, and therefore lies
  entirely inside it.
-/

@[expose] public section

open Order Set Set.Notation TopologicalSpace

/-- The Krull dimension of a topological space is `⊥` exactly when the space is empty. -/
theorem topologicalKrullDim_eq_bot_iff {X : Type*} [TopologicalSpace X] :
    topologicalKrullDim X = ⊥ ↔ IsEmpty X := by
  rw [topologicalKrullDim, krullDim_eq_bot_iff]
  exact ⟨fun h ↦ ⟨fun x ↦ h.elim ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩,
    fun h ↦ ⟨fun Z ↦ h.elim Z.isIrreducible.nonempty.some⟩⟩

/-- The subspace `univ` of a topological space has the Krull dimension of the space. -/
theorem topologicalKrullDim_univ (X : Type*) [TopologicalSpace X] :
    topologicalKrullDim (univ : Set X) = topologicalKrullDim X :=
  IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph

/-- Let `Z ⊆ S` be subsets of a topological space, with `Z` closed in `S`. If no maximal
irreducible subset of `S` is contained in `Z`, then `dim Z + 1 ≤ dim S`.

Indeed a chain of irreducible closed subsets of `Z` is a chain of irreducible closed subsets of
`S`; its largest member is contained in some irreducible component of `S`, which by hypothesis
is not contained in `Z` and is therefore strictly larger than every member of the chain. So
appending it to the chain gives a chain of length one more. -/
theorem topologicalKrullDim_add_one_le_of_forall_maximal {X : Type*} [TopologicalSpace X]
    {S Z : Set X} (hZS : Z ⊆ S) (hZ : IsClosed (S ↓∩ Z))
    (h : ∀ T, Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) T → ¬T ⊆ Z) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim S := by
  rcases eq_empty_or_nonempty Z with rfl | hZne
  · rw [show topologicalKrullDim (∅ : Set X) = ⊥ from
      topologicalKrullDim_eq_bot_iff.2 inferInstance, WithBot.bot_add]
    exact bot_le
  have : Nonempty Z := hZne.to_subtype
  have : Nonempty (IrreducibleCloseds Z) :=
    ⟨⟨closure {Classical.arbitrary Z}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have : Nonempty S := (hZne.mono hZS).to_subtype
  have : Nonempty (IrreducibleCloseds S) :=
    ⟨⟨closure {Classical.arbitrary S}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hincl : Topology.IsInducing (inclusion hZS) :=
    (Topology.IsEmbedding.inclusion hZS).isInducing
  rw [topologicalKrullDim, topologicalKrullDim, krullDim_eq_iSup_length,
    krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add, ENat.iSup_add,
    WithBot.coe_le_coe, iSup_le_iff]
  intro l
  obtain ⟨W, hWdef⟩ : ∃ W : IrreducibleCloseds S,
      W = IrreducibleCloseds.map (inclusion hZS) hincl.continuous l.last := ⟨_, rfl⟩
  obtain ⟨T, hTmem, hTsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (W : Set S) W.isIrreducible
  have hWZ : (W : Set S) ⊆ S ↓∩ Z := by
    rw [hWdef, IrreducibleCloseds.coe_map]
    refine closure_minimal ?_ hZ
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hTZ : ¬ ((T : Set S) ⊆ S ↓∩ Z) := fun hc ↦
    h _ (maximal_isIrreducible_image_val_of_mem_irreducibleComponents hTmem)
      (image_subset_iff.2 hc)
  have hlt : W < ⟨T, hTmem.1, isClosed_of_mem_irreducibleComponents T hTmem⟩ := by
    refine lt_of_le_of_ne hTsub fun heq ↦ hTZ ?_
    have hcoe : (W : Set S) = T := congrArg _ heq
    exact hcoe ▸ hWZ
  refine le_trans ?_ (le_iSup _
    ((l.map _ (IrreducibleCloseds.map_strictMono_of_isInducing hincl)).snoc _ (hWdef ▸ hlt)))
  simp

/-- Let `Z ⊆ S` be subsets of a topological space, with `Z` closed in `S` and `S` nonempty of
finite dimension. If no maximal irreducible subset of `S` is contained in `Z`, then
`dim Z < dim S`. -/
theorem topologicalKrullDim_lt_of_forall_maximal {X : Type*} [TopologicalSpace X]
    {S Z : Set X} (hZS : Z ⊆ S) (hZ : IsClosed (S ↓∩ Z)) (hS : S.Nonempty)
    (hfin : topologicalKrullDim S ≠ ⊤)
    (h : ∀ T, Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) T → ¬T ⊆ Z) :
    topologicalKrullDim Z < topologicalKrullDim S := by
  have hle := topologicalKrullDim_add_one_le_of_forall_maximal hZS hZ h
  have hSbot : topologicalKrullDim S ≠ ⊥ := by
    rw [Ne, topologicalKrullDim_eq_bot_iff, not_isEmpty_iff]
    exact hS.to_subtype
  obtain ⟨m, hm⟩ : ∃ m : ℕ, topologicalKrullDim S = m := by
    lift topologicalKrullDim S to ℕ∞ using hSbot with d hd
    lift d to ℕ using (by simpa using hfin) with m
    exact ⟨m, by norm_cast⟩
  rw [hm] at hle ⊢
  exact ENat.WithBot.add_one_le_natCast_iff.mp hle

/-- If `Z` is a proper closed subset of an irreducible topological space `X`, then the Krull
dimension of `Z` is at least one less than the Krull dimension of `X`.

This is the case `S = univ` of `topologicalKrullDim_add_one_le_of_forall_maximal`: in an
irreducible space the only maximal irreducible subset of `univ` is `univ` itself. -/
theorem topologicalKrullDim_add_one_le {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    {Z : Set X} (hZc : IsClosed Z) (hZ : Z ≠ univ) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim X := by
  rw [← topologicalKrullDim_univ X]
  exact topologicalKrullDim_add_one_le_of_forall_maximal (subset_univ Z)
    (hZc.preimage continuous_subtype_val)
    fun _ hT hTZ ↦ hZ (univ_subset_iff.1 (eq_univ_of_maximal_isIrreducible hT ▸ hTZ))

/-- **The Krull dimension of a subset is monotone in the subset.** -/
theorem topologicalKrullDim_le_of_subset {X : Type*} [TopologicalSpace X] {Z S : Set X}
    (hZS : Z ⊆ S) : topologicalKrullDim Z ≤ topologicalKrullDim S :=
  (Topology.IsEmbedding.inclusion hZS).isInducing.topologicalKrullDim_le

/-- **The dimension of a subset is controlled by the dimensions of its maximal irreducible
subsets**: to bound `dim S` it is enough to bound `dim T` for every maximal irreducible subset
`T` of `S`.

A chain of irreducible closed subsets of `S` has its largest member contained in some maximal
irreducible subset `T` of `S`; the whole chain then lies in `T`, and intersecting it with `T`
gives a chain of the same length of irreducible closed subsets of `T`. -/
theorem topologicalKrullDim_le_of_forall_maximal {X : Type*} [TopologicalSpace X] {S : Set X}
    {d : WithBot ℕ∞}
    (h : ∀ T, Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) T → topologicalKrullDim T ≤ d) :
    topologicalKrullDim S ≤ d := by
  rw [topologicalKrullDim, krullDim]
  refine iSup_le fun l ↦ ?_
  obtain ⟨T, hTmem, hTsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (l.last : Set S) l.last.isIrreducible
  have hsub : ∀ i, (l i : Set S) ⊆ T := fun i ↦
    (SetLike.coe_subset_coe.2 (l.monotone (Fin.le_last i))).trans hTsub
  have himg : ∀ i, ((↑) '' (T ↓∩ (l i : Set S)) : Set S) = (l i : Set S) := fun i ↦ by
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 (hsub i)]
  let f : Fin (l.length + 1) → IrreducibleCloseds T := fun i ↦
    ⟨T ↓∩ (l i : Set S), (isIrreducible_preimage_val_iff (hsub i)).2 (l i).isIrreducible,
      (l i).isClosed.preimage continuous_subtype_val⟩
  have hfinj : ∀ i j, f i = f j → l i = l j := fun i j hij ↦ by
    refine IrreducibleCloseds.ext ?_
    rw [← himg i, ← himg j]
    exact congrArg _ (congrArg (fun Z : IrreducibleCloseds T ↦ (Z : Set T)) hij)
  let l' : LTSeries (IrreducibleCloseds T) :=
    { length := l.length
      toFun := f
      step := fun i ↦ by
        have hst : l i.castSucc < l i.succ := l.step i
        have hcoe : ((l i.castSucc : Set S)) ⊆ (l i.succ : Set S) := hst.le
        have hle : f i.castSucc ≤ f i.succ := fun x hx ↦ hcoe hx
        change f i.castSucc < f i.succ
        exact lt_of_le_of_ne hle fun heq ↦ hst.ne (hfinj _ _ heq) }
  calc (l.length : WithBot ℕ∞) = (l'.length : WithBot ℕ∞) := rfl
    _ ≤ krullDim (IrreducibleCloseds T) := l'.length_le_krullDim
    _ = topologicalKrullDim (((↑) '' T : Set X)) :=
        IsHomeomorph.topologicalKrullDim_eq _
          (Topology.IsEmbedding.subtypeVal.homeomorphImage T).isHomeomorph
    _ ≤ d := h _ (maximal_isIrreducible_image_val_of_mem_irreducibleComponents hTmem)
