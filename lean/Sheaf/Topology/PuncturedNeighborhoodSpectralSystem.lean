/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Topology.PuncturedNeighborhoodCohomologyDiagram
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
import Sheaf.Topology.SpectralDirectedLimit

/-! # The inverse system of punctured compact open neighborhoods

Source: Stacks Project, Topology, Tags 0A31, 0902 and 0AP0.
(blueprint: lem-weil-pbc-punctured-neighborhood-spectral-system)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace Opposite Topology Set
namespace TopCat

/-- Compact open neighborhoods ordered by reverse inclusion.
Source: Stacks Project, Topology, Tags 0A31, 0902 and 0AP0.
(blueprint: lem-weil-pbc-punctured-neighborhood-spectral-system) -/
abbrev puncturedNeighborhoodIndex {T : Type u} [TopologicalSpace T] (Z : Set T) :=
  (compactOpenNeighborhoods Z)ᵒᵈ

/-- The punctured open subspace at an index.
Source: Stacks Project, Topology, Tags 0A31, 0902 and 0AP0.
(blueprint: lem-weil-pbc-punctured-neighborhood-spectral-system) -/
def puncturedNeighborhoodSpace {T : Type u} [TopologicalSpace T]
    (Z : Set T) (hZ : IsClosed Z) (i : puncturedNeighborhoodIndex Z) : TopCat.{u} :=
  TopCat.of (puncturedNeighborhoodOpen Z hZ (OrderDual.ofDual i))

/-- The transition inclusion of punctured neighborhoods.
Source: Stacks Project, Topology, Tags 0A31, 0902 and 0AP0.
(blueprint: lem-weil-pbc-punctured-neighborhood-spectral-system) -/
def puncturedNeighborhoodTransition {T : Type u} [TopologicalSpace T]
    (Z : Set T) (hZ : IsClosed Z) (i j : puncturedNeighborhoodIndex Z) (h : i ≤ j) :
    puncturedNeighborhoodSpace Z hZ j ⟶ puncturedNeighborhoodSpace Z hZ i :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.val, h x.property.1, x.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The projection from the punctured generalization subspace.
Source: Stacks Project, Topology, Tags 0A31, 0902 and 0AP0.
(blueprint: lem-weil-pbc-punctured-neighborhood-spectral-system) -/
def puncturedNeighborhoodProjection {T : Type u} [TopologicalSpace T]
    (Z : Set T) (hZ : IsClosed Z) (i : puncturedNeighborhoodIndex Z) :
    TopCat.of (puncturedGeneralizations Z) ⟶ puncturedNeighborhoodSpace Z hZ i :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.val,
    puncturedGeneralizations_le_preimage Z hZ (OrderDual.ofDual i) (show x ∈ ⊤ by trivial)⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The whole space is a compact open neighborhood.
Source: Stacks Project, Topology, Tags 0A31, 0902 and 0AP0.
(blueprint: lem-weil-pbc-punctured-neighborhood-spectral-system) -/
theorem puncturedNeighborhoodIndex_nonempty {T : Type u} [TopologicalSpace T]
    [CompactSpace T] (Z : Set T) : Nonempty (puncturedNeighborhoodIndex Z) :=
  ⟨⟨⊤, subset_univ _, isCompact_univ⟩⟩

/-- Intersection gives a common later neighborhood.
Source: Stacks Project, Topology, Tags 0A31, 0902 and 0AP0.
(blueprint: lem-weil-pbc-punctured-neighborhood-spectral-system) -/
theorem puncturedNeighborhoodIndex_directed {T : Type u} [TopologicalSpace T]
    [QuasiSeparatedSpace T] (Z : Set T) : IsDirected (puncturedNeighborhoodIndex Z) (· ≤ ·) :=
  ⟨fun i j ↦ ⟨⟨i.val ⊓ j.val, (fun _ hz ↦ ⟨i.property.1 hz, j.property.1 hz⟩),
    i.property.2.inter_of_isOpen j.property.2 i.val.isOpen j.val.isOpen⟩,
      (fun _ hx ↦ hx.1), (fun _ hx ↦ hx.2)⟩⟩

/-- Each puncture is a compact open spectral space.
Source: Stacks Project, Topology, Tags 0A31, 0902 and 0AP0.
(blueprint: lem-weil-pbc-punctured-neighborhood-spectral-system) -/
theorem puncturedNeighborhoodSpace_spectral {T : Type u} [TopologicalSpace T]
    [SpectralSpace T] (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (i : puncturedNeighborhoodIndex Z) : SpectralSpace (puncturedNeighborhoodSpace Z hZ i) := by
  have hc : IsCompact (puncturedNeighborhoodOpen Z hZ (OrderDual.ofDual i) : Set T) :=
    i.property.2.inter_of_isOpen hU i.val.isOpen hZ.isOpen_compl
  let := isCompact_iff_compactSpace.mp hc
  exact (puncturedNeighborhoodOpen Z hZ (OrderDual.ofDual i)).isOpen.isOpenEmbedding_subtypeVal
    |>.spectralSpace

/-- Transition inclusions are spectral, by quasi-separatedness of the ambient space.
Source: Stacks Project, Topology, Tags 0A31, 0902 and 0AP0.
(blueprint: lem-weil-pbc-punctured-neighborhood-spectral-system) -/
theorem puncturedNeighborhoodTransition_spectral {T : Type u} [TopologicalSpace T]
    [SpectralSpace T] (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (i j : puncturedNeighborhoodIndex Z) (h : i ≤ j) :
    IsSpectralMap (puncturedNeighborhoodTransition Z hZ i j h) := by
  refine ⟨(puncturedNeighborhoodTransition Z hZ i j h).hom.continuous, ?_⟩
  intro V hVo hVc
  let Vi : Opens T := puncturedNeighborhoodOpen Z hZ (OrderDual.ofDual i)
  let Vj : Opens T := puncturedNeighborhoodOpen Z hZ (OrderDual.ofDual j)
  have hVc' : IsCompact (Subtype.val '' V : Set T) := hVc.image continuous_subtype_val
  have hVo' : IsOpen (Subtype.val '' V : Set T) :=
    Vi.isOpen.isOpenEmbedding_subtypeVal.isOpenMap V hVo
  have hVjc : IsCompact (Vj : Set T) :=
    j.property.2.inter_of_isOpen hU j.val.isOpen hZ.isOpen_compl
  apply (IsEmbedding.subtypeVal.isCompact_iff).mpr
  convert hVc'.inter_of_isOpen hVjc hVo' Vj.isOpen using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨_, hy, rfl⟩, y.property⟩
  · rintro ⟨⟨y, hy, rfl⟩, hj⟩
    refine ⟨⟨y.val, hj⟩, ?_, rfl⟩
    change (⟨y.val, _⟩ : Vi) ∈ V
    exact hy

private theorem mem_all_neighborhoods {T : Type u} [TopologicalSpace T] [SpectralSpace T]
    (Z : Set T) (hZ : IsClosed Z) (x : T)
    (hx : ∀ i : compactOpenNeighborhoods Z, x ∈ i.val) :
    (closure ({x} : Set T) ∩ Z).Nonempty := by
  classical
  by_contra hn
  have hdis : Z ⊆ (closure ({x} : Set T))ᶜ := by
    intro z hz hzx
    exact hn ⟨z, hzx, hz⟩
  let B := {V : Opens T // IsCompact (V : Set T) ∧ (V : Set T) ⊆ (closure {x})ᶜ}
  have hcover : Z ⊆ ⋃ V : B, (V.val : Set T) := by
    intro z hz
    obtain ⟨V, ⟨hVo, hVc⟩, hzV, hV⟩ :=
      (PrespectralSpace.isTopologicalBasis (X := T)).exists_subset_of_mem_open
        (hdis hz) isClosed_closure.isOpen_compl
    exact mem_iUnion.mpr ⟨⟨⟨V, hVo⟩, hVc, hV⟩, hzV⟩
  obtain ⟨s, hs⟩ := hZ.isCompact.elim_finite_subcover (fun V : B ↦ (V.val : Set T))
    (fun V ↦ V.val.isOpen) hcover
  let N : Opens T := ⟨⋃ V ∈ s, (V.val : Set T),
    isOpen_biUnion (fun V _ ↦ V.val.isOpen)⟩
  have hNc : IsCompact (N : Set T) := s.isCompact_biUnion fun V _ ↦ V.property.1
  have hxN := hx ⟨N, hs, hNc⟩
  obtain ⟨V, _, hxV⟩ := mem_iUnion₂.mp hxN
  exact V.property.2 hxV (subset_closure (mem_singleton x))

/-- The punctured generalizations, with their subspace topology, are the topological limit.

Source: Stacks Project, Topology, Tags 0A31 and 0AP0. Proof: a point lies in every
compact open neighborhood of Z exactly when its closure meets Z. To exclude a point
whose closure misses Z, cover the compact closed set Z by compact basis opens in the
complement of that closure, and take their finite union. Compatible tuples in the
punctures have one ambient value (compare each index with the whole-space index).
That value lies in all neighborhoods and outside Z. Conversely every punctured
generalization gives such a tuple. The whole-space coordinate already induces the
subspace topology; continuity of the other coordinates gives the reverse inequality.
Source: Stacks Project, Topology, Tags 0A31, 0902 and 0AP0.
(blueprint: lem-weil-pbc-punctured-neighborhood-spectral-system) -/
theorem puncturedNeighborhood_topologicalLimit {T : Type u} [TopologicalSpace T]
    [SpectralSpace T] (Z : Set T) (hZ : IsClosed Z) :
    (∀ a : ∀ i : puncturedNeighborhoodIndex Z, puncturedNeighborhoodSpace Z hZ i,
      (∀ i j (h : i ≤ j), puncturedNeighborhoodTransition Z hZ i j h (a j) = a i) →
      ∃! x : puncturedGeneralizations Z,
        ∀ i, puncturedNeighborhoodProjection Z hZ i x = a i) ∧
    (TopCat.of (puncturedGeneralizations Z)).str =
      ⨅ i : puncturedNeighborhoodIndex Z,
        TopologicalSpace.induced (puncturedNeighborhoodProjection Z hZ i)
          (puncturedNeighborhoodSpace Z hZ i).str := by
  let t : puncturedNeighborhoodIndex Z := ⟨⊤, subset_univ _, isCompact_univ⟩
  constructor
  · intro a ha
    have hv (i : puncturedNeighborhoodIndex Z) : (a i).val = (a t).val :=
      congrArg Subtype.val (ha t i (show t ≤ i from subset_univ _))
    have hx : (a t).val ∈ puncturedGeneralizations Z :=
      ⟨mem_all_neighborhoods Z hZ (a t).val (fun i ↦ hv i ▸ (a i).property.1),
        (a t).property.2⟩
    refine ⟨⟨(a t).val, hx⟩, (fun i ↦ Subtype.ext (hv i).symm), ?_⟩
    intro y hy
    apply Subtype.ext
    exact congrArg (fun z : puncturedNeighborhoodSpace Z hZ t ↦ z.val) (hy t)
  · apply le_antisymm
    · apply le_iInf
      intro i
      exact (puncturedNeighborhoodProjection Z hZ i).hom.continuous.le_induced
    · apply (iInf_le _ t).trans
      change TopologicalSpace.induced (puncturedNeighborhoodProjection Z hZ t)
        (TopologicalSpace.induced Subtype.val inferInstance) ≤
          TopologicalSpace.induced Subtype.val inferInstance
      rw [induced_compose]
      exact le_rfl

/-- The punctured generalization space is spectral when the complement of `Z` is compact.
Source: Stacks Project, Topology, Tags 0A31, 0902 and 0AP0.
(blueprint: lem-weil-pbc-punctured-neighborhood-spectral-system) -/
theorem puncturedGeneralizations_spectral {T : Type u} [TopologicalSpace T]
    [SpectralSpace T] (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ) :
    SpectralSpace (puncturedGeneralizations Z) := by
  let I := puncturedNeighborhoodIndex Z
  let S : I → TopCat.{u} := puncturedNeighborhoodSpace Z hZ
  let f : ∀ i j : I, i ≤ j → (S j ⟶ S i) := puncturedNeighborhoodTransition Z hZ
  let X : TopCat.{u} := TopCat.of (puncturedGeneralizations Z)
  let p : ∀ i : I, X ⟶ S i := puncturedNeighborhoodProjection Z hZ
  let : Nonempty I := puncturedNeighborhoodIndex_nonempty Z
  let : IsDirected I (· ≤ ·) := puncturedNeighborhoodIndex_directed Z
  let : ∀ j : I, SpectralSpace (S j) := puncturedNeighborhoodSpace_spectral Z hZ hU
  have hf (j k : I) (h : j ≤ k) : IsSpectralMap (f j k h) :=
    puncturedNeighborhoodTransition_spectral Z hZ hU j k h
  have hfid (j : I) : f j j le_rfl = 𝟙 (S j) := TopCat.ext fun _ ↦ Subtype.ext rfl
  have hfcomp (j k l : I) (hjk : j ≤ k) (hkl : k ≤ l) :
      f k l hkl ≫ f j k hjk = f j l (hjk.trans hkl) :=
    TopCat.ext fun _ ↦ Subtype.ext rfl
  have hpcomp (j k : I) (h : j ≤ k) : p k ≫ f j k h = p j :=
    TopCat.ext fun _ ↦ Subtype.ext rfl
  obtain ⟨hlimit, htop⟩ := puncturedNeighborhood_topologicalLimit Z hZ
  have hinj : Function.Injective (fun x : X ↦ fun j : I ↦ p j x) := by
    let t : I := ⟨⊤, Set.subset_univ _, isCompact_univ⟩
    intro x y h
    exact Subtype.ext (congrArg (fun z : S t ↦ z.val) (congrFun h t))
  exact (Topology.spectralSpace_directedLimit
    (fun j : I ↦ S j) (fun j k h ↦ f j k h) hf
    (fun _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl)
    X (fun j ↦ p j) (fun j ↦ (p j).hom.continuous)
    (fun _ _ _ ↦ rfl) hinj
    (fun a ha ↦ by obtain ⟨x, hx, _⟩ := hlimit a ha; exact ⟨x, hx⟩) htop).1

end TopCat
