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
* `Topology.IsInducing.topologicalKrullDim_le_of_range_subset`: a space that embeds into a
  subset `S` of a topological space has dimension at most `dim S`; `topologicalKrullDim_mono`,
  the monotonicity of `dim` in the subset, is the special case of an inclusion.
* `TopologicalSpace.IrreducibleCloseds.height_eq_topologicalKrullDim`: the height of an
  irreducible closed subset `T` of a space is the dimension of `T` as a subspace.
* `topologicalKrullDim_eq_iSup_irreducibleComponents`: **the dimension of a space is the
  supremum of the dimensions of its irreducible components**;
  `topologicalKrullDim_eq_iSup_maximal` is its form for a subset `S` of a space, whose
  irreducible components are the maximal irreducible subsets of `S`.
* `coheight_add_topologicalKrullDim_closure_le`: in a sober space, `codim z + dim (closure {z})`
  is at most the dimension of the space, for any point `z`.
-/

@[expose] public section

open Order Set Set.Notation TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The Krull dimension of a topological space is `⊥` exactly when the space is empty. -/
theorem topologicalKrullDim_eq_bot_iff :
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
theorem topologicalKrullDim_add_one_le_of_forall_maximal {S Z : Set X} (hZS : Z ⊆ S)
    (hZ : IsClosed (S ↓∩ Z))
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
theorem topologicalKrullDim_lt_of_forall_maximal {S Z : Set X} (hZS : Z ⊆ S)
    (hZ : IsClosed (S ↓∩ Z)) (hS : S.Nonempty)
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
theorem topologicalKrullDim_add_one_le [IrreducibleSpace X] {Z : Set X} (hZc : IsClosed Z)
    (hZ : Z ≠ univ) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim X := by
  rw [← topologicalKrullDim_univ X]
  exact topologicalKrullDim_add_one_le_of_forall_maximal (subset_univ Z)
    (hZc.preimage continuous_subtype_val)
    fun _ hT hTZ ↦ hZ (univ_subset_iff.1 (eq_univ_of_maximal_isIrreducible hT ▸ hTZ))

/-- A space that embeds into a subset `S` of a topological space has Krull dimension at most
that of `S`. -/
theorem Topology.IsInducing.topologicalKrullDim_le_of_range_subset {f : Y → X}
    (hf : IsInducing f) {S : Set X} (hfS : range f ⊆ S) :
    topologicalKrullDim Y ≤ topologicalKrullDim S :=
  (IsInducing.of_comp (hf.continuous.subtype_mk fun y ↦ hfS ⟨y, rfl⟩)
    continuous_subtype_val hf).topologicalKrullDim_le

/-- The Krull dimension of a subset is monotone in the subset. -/
theorem topologicalKrullDim_mono {Z S : Set X} (hZS : Z ⊆ S) :
    topologicalKrullDim Z ≤ topologicalKrullDim S :=
  (Topology.IsEmbedding.inclusion hZS).isInducing.topologicalKrullDim_le

/-- A subset of a subspace `S` of `X` has the same Krull dimension seen in `S` and seen in `X`. -/
theorem topologicalKrullDim_image_val {S : Set X} (Z : Set S) :
    topologicalKrullDim ((↑) '' Z : Set X) = topologicalKrullDim Z :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (Topology.IsEmbedding.subtypeVal.homeomorphImage Z).isHomeomorph).symm

/-- The height of an irreducible closed subset `T` of a topological space is the Krull dimension
of `T` as a subspace: the irreducible closed subsets of `T` are exactly the irreducible closed
subsets of the space contained in `T`. -/
theorem TopologicalSpace.IrreducibleCloseds.height_eq_topologicalKrullDim
    (T : IrreducibleCloseds X) :
    (height T : WithBot ℕ∞) = topologicalKrullDim (T : Set X) := by
  rw [height_eq_krullDim_Iic, ← krullDim_eq_of_orderIso (orderIsoIic T), ← topologicalKrullDim]

/-- The height of an irreducible closed subset `T` of a subspace `S` is the Krull dimension of
`T`, seen as a subspace of the ambient space. -/
theorem TopologicalSpace.IrreducibleCloseds.height_eq_topologicalKrullDim_image {S : Set X}
    (T : IrreducibleCloseds S) :
    (height T : WithBot ℕ∞) = topologicalKrullDim ((↑) '' (T : Set S) : Set X) :=
  T.height_eq_topologicalKrullDim.trans (topologicalKrullDim_image_val _).symm

/-- **The dimension of a topological space is the supremum of the dimensions of its irreducible
components.**

Every irreducible closed subset is contained in an irreducible component `Z`, so its height is
at most `dim Z` by `TopologicalSpace.IrreducibleCloseds.height_eq_topologicalKrullDim`;
conversely every component is a subspace. -/
theorem topologicalKrullDim_eq_iSup_irreducibleComponents :
    topologicalKrullDim X = ⨆ Z ∈ irreducibleComponents X, topologicalKrullDim Z := by
  refine le_antisymm ?_ (iSup₂_le fun Z _ ↦ topologicalKrullDim_subspace_le X Z)
  rw [topologicalKrullDim, krullDim_eq_iSup_height]
  refine iSup_le fun W ↦ ?_
  obtain ⟨Z, hZmem, hZsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (W : Set X) W.isIrreducible
  let Z' : IrreducibleCloseds X := ⟨Z, hZmem.1, isClosed_of_mem_irreducibleComponents Z hZmem⟩
  calc (height W : WithBot ℕ∞) ≤ (height Z' : WithBot ℕ∞) := mod_cast height_mono (hZsub : W ≤ Z')
    _ = topologicalKrullDim (Z : Set X) := Z'.height_eq_topologicalKrullDim
    _ ≤ _ := le_biSup (fun Z : Set X ↦ topologicalKrullDim Z) hZmem

/-- **The dimension of a subset is the supremum of the dimensions of its maximal irreducible
subsets**: the form of `topologicalKrullDim_eq_iSup_irreducibleComponents` for the subspace `S`,
whose irreducible components are the maximal irreducible subsets of `S`. -/
theorem topologicalKrullDim_eq_iSup_maximal {S : Set X} :
    topologicalKrullDim S =
      ⨆ (T : Set X) (_ : Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) T), topologicalKrullDim T := by
  refine le_antisymm ?_ (iSup₂_le fun T hT ↦ topologicalKrullDim_mono hT.prop.2)
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents]
  refine iSup₂_le fun Z hZ ↦ (topologicalKrullDim_image_val Z).ge.trans
    (le_biSup (fun T : Set X ↦ topologicalKrullDim T)
      (maximal_isIrreducible_image_val_of_mem_irreducibleComponents hZ))

attribute [local instance] specializationOrder in
/-- **The chains through a point concatenate**: in a sober space, the codimension of a point `z`
plus the dimension of the closure of `z` is at most the dimension of the space.

Indeed the chains of irreducible closed subsets contained in `closure {z}` and the chains of
irreducible closed subsets containing it splice together at `closure {z}`. -/
theorem coheight_add_topologicalKrullDim_closure_le [QuasiSober X] [T0Space X] (z : X) :
    (coheight z : WithBot ℕ∞) + topologicalKrullDim (closure {z} : Set X) ≤
      topologicalKrullDim X := by
  have : Nonempty (IrreducibleCloseds X) := ⟨irreducibleSetEquivPoints.symm z⟩
  calc (coheight z : WithBot ℕ∞) + topologicalKrullDim (closure {z} : Set X)
      = ((height (irreducibleSetEquivPoints.symm z) +
          coheight (irreducibleSetEquivPoints.symm z) : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add, coheight_orderIso,
          (irreducibleSetEquivPoints.symm z).height_eq_topologicalKrullDim,
          coe_irreducibleEquivPoints_symm_apply, add_comm]
    _ ≤ topologicalKrullDim X := by
        rw [topologicalKrullDim, krullDim_eq_iSup_height_add_coheight_of_nonempty]
        exact WithBot.coe_le_coe.2 (le_iSup (fun T ↦ height T + coheight T) _)
