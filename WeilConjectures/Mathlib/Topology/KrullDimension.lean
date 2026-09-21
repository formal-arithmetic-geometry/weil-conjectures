/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.Irreducible
public import WeilConjectures.Mathlib.Topology.Sets.Closeds

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
* `topologicalKrullDim_le_of_isInducing_of_range_subset`: a space that embeds into a subset `S`
  of a topological space has dimension at most `dim S`; `topologicalKrullDim_mono`, the
  monotonicity of `dim` in the subset, is the special case of an inclusion.
* `height_eq_topologicalKrullDim`: the height of an irreducible closed subset `T` of a subspace
  `S` is the dimension of `T`, seen as a subspace of the ambient space.
* `topologicalKrullDim_eq_iSup_maximal`: **the dimension of a subset is the supremum of the
  dimensions of its maximal irreducible subsets.** `topologicalKrullDim_le_of_forall_maximal` is
  the resulting bound on `dim S`.
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

/-- A space that embeds into a subset `S` of a topological space has Krull dimension at most
that of `S`. -/
theorem topologicalKrullDim_le_of_isInducing_of_range_subset {Y X : Type*} [TopologicalSpace Y]
    [TopologicalSpace X] {f : Y → X} (hf : Topology.IsInducing f) {S : Set X}
    (hfS : range f ⊆ S) : topologicalKrullDim Y ≤ topologicalKrullDim S :=
  (Topology.IsInducing.of_comp (hf.continuous.subtype_mk fun y ↦ hfS ⟨y, rfl⟩)
    continuous_subtype_val hf).topologicalKrullDim_le

/-- The Krull dimension of a subset is monotone in the subset. -/
theorem topologicalKrullDim_mono {X : Type*} [TopologicalSpace X] {Z S : Set X}
    (hZS : Z ⊆ S) : topologicalKrullDim Z ≤ topologicalKrullDim S :=
  topologicalKrullDim_le_of_isInducing_of_range_subset Topology.IsEmbedding.subtypeVal.isInducing
    (Subtype.range_coe.trans_subset hZS)

/-- The height of an irreducible closed subset `T` of a subspace `S` is the Krull dimension of
`T`, seen as a subspace of the ambient space: the irreducible closed subsets of `T` are exactly
the irreducible closed subsets of `S` contained in `T`. -/
theorem height_eq_topologicalKrullDim {X : Type*} [TopologicalSpace X] {S : Set X}
    (T : IrreducibleCloseds S) :
    (height T : WithBot ℕ∞) = topologicalKrullDim ((↑) '' (T : Set S) : Set X) := by
  rw [height_eq_krullDim_Iic, ← krullDim_eq_of_orderIso (IrreducibleCloseds.orderIsoIic T),
    ← topologicalKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Topology.IsEmbedding.subtypeVal.homeomorphImage (T : Set S)).isHomeomorph

/-- **The dimension of a subset is the supremum of the dimensions of its maximal irreducible
subsets.**

Every irreducible closed subset of `S` is contained in a maximal irreducible subset `T` of `S`,
so its height is at most `dim T` by `height_eq_topologicalKrullDim`; conversely every such `T`
is a subset of `S`. -/
theorem topologicalKrullDim_eq_iSup_maximal {X : Type*} [TopologicalSpace X] {S : Set X} :
    topologicalKrullDim S =
      ⨆ T ∈ {T : Set X | Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) T}, topologicalKrullDim T := by
  refine le_antisymm ?_ (iSup₂_le fun T hT ↦ topologicalKrullDim_mono hT.1.2)
  rw [topologicalKrullDim, krullDim_eq_iSup_height]
  refine iSup_le fun W ↦ ?_
  obtain ⟨T, hTmem, hTsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (W : Set S) W.isIrreducible
  let T' : IrreducibleCloseds S := ⟨T, hTmem.1, isClosed_of_mem_irreducibleComponents T hTmem⟩
  calc (height W : WithBot ℕ∞) ≤ (height T' : WithBot ℕ∞) := by
        exact_mod_cast height_mono (show W ≤ T' from hTsub)
    _ = topologicalKrullDim ((↑) '' (T' : Set S) : Set X) := height_eq_topologicalKrullDim T'
    _ ≤ _ := le_biSup (fun Z : Set X ↦ topologicalKrullDim Z)
        (maximal_isIrreducible_image_val_of_mem_irreducibleComponents hTmem)

/-- **The dimension of a subset is controlled by the dimensions of its maximal irreducible
subsets**: to bound `dim S` it is enough to bound `dim T` for every maximal irreducible subset
`T` of `S`. -/
theorem topologicalKrullDim_le_of_forall_maximal {X : Type*} [TopologicalSpace X] {S : Set X}
    {d : WithBot ℕ∞}
    (h : ∀ T, Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) T → topologicalKrullDim T ≤ d) :
    topologicalKrullDim S ≤ d :=
  topologicalKrullDim_eq_iSup_maximal.trans_le (iSup₂_le h)
