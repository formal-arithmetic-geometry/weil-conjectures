/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.KrullDimension
public import Sheaf.Topology.PuncturedNeighborhoodCohomologyDiagram
import WeilConjectures.Topology.SpectralGeneralizations
import Sheaf.Topology.SpectralDirectedLimit

/-! # Spectrality and dimension of punctured generalization neighborhoods

Source: Stacks Project, Topology, Tag 0AP0; Cohomology, Tag 0A3G, induction step (2).
(blueprint: lem-sfb-punctured-spectral-neighborhood-dimension)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Topology

/-- The generalizations of a closed subset with quasi-compact open complement, after
removing that subset, form a spectral space of dimension at most one less than the
ambient dimension bound.

Source: Stacks Project, Topology, Tag 0AP0 (`lemma-make-spectral-space-minus`), and
Cohomology, Tag 0A3G (`proposition-cohomological-dimension-spectral`), induction step (2).
(blueprint: lem-sfb-punctured-spectral-neighborhood-dimension)

Proof:
1. Put U = X \ Z and W = {x | closure {x} meets Z}. Closedness makes Z compact.
By `lem-weil-pbc-spectral-generalizations-of-quasi-compact`, W is the intersection
of all compact open neighborhoods N of Z. These neighborhoods contain X as a member
and are directed under reverse inclusion, since intersections of compact opens are compact.
Thus S = W \ Z is the intersection of the compact opens N ∩ U.
2. Each N ∩ U is spectral: the ambient compact-open basis and finite-intersection
property restrict to this compact open subspace. For sobriety, take the ambient closure
of an irreducible closed subset of N ∩ U. Its ambient generic point lies in the open
N ∩ U, and is the unique generic point of the original subset. The transition inclusions
are spectral, because inverse images of compact opens are intersections of compact opens.
3. The inclusions exhibit S as the inverse limit of these subspaces: compatibility
identifies all coordinates with one ambient point, using the coordinate at intersections.
Such a point is precisely in S. The coordinate N = X induces the subspace topology.
Apply `lem-weil-pbc-spectral-directed-limit-spectral` to obtain spectrality of S.
4. For a strict chain C₀ ⊊ ⋯ ⊊ Cₘ of irreducible closed subsets of S, choose their
generic points ηᵢ. Their ambient closures Dᵢ form a strict chain in X: intersecting
with S recovers Cᵢ, and ηᵢ ∈ Dᵢ₊₁ gives inclusion of the ambient closures.
5. Since η₀ is in W, choose z in Z ∩ closure {η₀}. The irreducible closed set
closure {z} lies in D₀ ∩ Z, strictly inside D₀ because η₀ is not in Z. Prepending
it gives a chain of length m + 1 in X. Thus m + 1 ≤ n and m ≤ n - 1.
Taking the supremum of all chain lengths proves the dimension bound.
6. If Z is empty, Z = X, or X is empty, S is empty. The directed index still
contains X, spectrality holds for the empty space, and its dimension is bottom (-∞).
No nonemptiness assumption was used except when testing an actual chain. -/
theorem spectralSpace_puncturedGeneralizations_and_dimension
    (X : Type u) [TopologicalSpace X] [SpectralSpace X]
    (n : ℕ) (hn : 1 ≤ n) (hdim : topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (Z : Set X) (hZ : IsClosed Z) (hU : IsCompact Zᶜ) :
    SpectralSpace (TopCat.puncturedGeneralizations Z) ∧
      topologicalKrullDim (TopCat.puncturedGeneralizations Z) ≤
        ((n - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  let I := OrderDual {N : Set X // IsOpen N ∧ IsCompact N ∧ Z ⊆ N}
  let topN : I := ⟨Set.univ, isOpen_univ, isCompact_univ, Set.subset_univ Z⟩
  let : Nonempty I := ⟨topN⟩
  let : IsDirected I (· ≤ ·) := ⟨fun i j ↦
    ⟨⟨i.val ∩ j.val, i.property.1.inter j.property.1,
      i.property.2.1.inter_of_isOpen j.property.2.1 i.property.1 j.property.1,
      fun z hz ↦ ⟨i.property.2.2 hz, j.property.2.2 hz⟩⟩,
      Set.inter_subset_left, Set.inter_subset_right⟩⟩
  let V (i : I) : Set X := i.val ∩ Zᶜ
  have hVo (i : I) : IsOpen (V i) := i.property.1.inter hZ.isOpen_compl
  have hVc (i : I) : IsCompact (V i) :=
    i.property.2.1.inter_of_isOpen hU i.property.1 hZ.isOpen_compl
  let Y (i : I) : Type u := V i
  let (i : I) : CompactSpace (Y i) := isCompact_iff_compactSpace.mp (hVc i)
  let (i : I) : SpectralSpace (Y i) := (hVo i).isOpenEmbedding_subtypeVal.spectralSpace
  let f (i j : I) (h : i ≤ j) : Y j → Y i :=
    fun x ↦ ⟨x.val, h x.property.1, x.property.2⟩
  have hfcont (i j : I) (h : i ≤ j) : Continuous (f i j h) :=
    continuous_subtype_val.subtype_mk _
  have hf (i j : I) (h : i ≤ j) : IsSpectralMap (f i j h) := by
    refine ⟨hfcont i j h, fun B ho hc ↦ ?_⟩
    rw [Subtype.isCompact_iff]
    have hBo : IsOpen (Subtype.val '' B : Set X) :=
      (hVo i).isOpenEmbedding_subtypeVal.isOpenMap _ ho
    have hBc : IsCompact (Subtype.val '' B : Set X) := hc.image continuous_subtype_val
    have heq : Subtype.val '' (f i j h ⁻¹' B) = (Subtype.val '' B : Set X) ∩ V j := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨f i j h y, hy, rfl⟩, y.property⟩
      · rintro ⟨⟨y, hy, rfl⟩, hj⟩
        exact ⟨⟨y.val, hj⟩, by simpa [f] using hy, rfl⟩
    rw [heq]
    exact hBc.inter_of_isOpen (hVc j) hBo (hVo j)
  have hmem (x : TopCat.puncturedGeneralizations Z) (i : I) : x.val ∈ V i := by
    obtain ⟨z, hz, hzZ⟩ := x.property.1
    exact ⟨(specializes_iff_mem_closure.mpr hz).mem_open i.property.1
      (i.property.2.2 hzZ), x.property.2⟩
  let p (i : I) : TopCat.puncturedGeneralizations Z → Y i :=
    fun x ↦ ⟨x.val, hmem x i⟩
  have hp (i : I) : Continuous (p i) := continuous_subtype_val.subtype_mk _
  have hspec : SpectralSpace (TopCat.puncturedGeneralizations Z) := by
    apply (spectralSpace_directedLimit Y f hf (fun _ ↦ rfl)
      (fun _ _ _ _ _ ↦ rfl) (TopCat.puncturedGeneralizations Z) p hp
      (fun _ _ _ ↦ funext fun _ ↦ Subtype.ext rfl) ?_ ?_ ?_).1
    · intro x y h
      apply Subtype.ext
      exact congrArg (fun t : Y topN ↦ t.val) (congrFun h topN)
    · intro s hs
      have heq (i : I) : (s i).val = (s topN).val :=
        congrArg Subtype.val (hs topN i (Set.subset_univ _))
      have hxW : (closure ({(s topN).val} : Set X) ∩ Z).Nonempty := by
        apply Set.nonempty_iff_ne_empty.mpr
        change (s topN).val ∈ {x : X | closure ({x} : Set X) ∩ Z ≠ ∅}
        rw [(generalizations_isCompact_sInter_isCompactOpen X Z hZ.isCompact).2]
        intro N hN
        exact heq ⟨N, hN⟩ ▸ (s ⟨N, hN⟩).property.1
      refine ⟨⟨(s topN).val, hxW, (s topN).property.2⟩, fun i ↦ ?_⟩
      exact Subtype.ext (heq i).symm
    · apply le_antisymm
      · exact le_iInf fun i ↦ (hp i).le_induced
      · exact (iInf_le _ topN).trans (by
          change TopologicalSpace.induced (p topN)
            (TopologicalSpace.induced Subtype.val ‹TopologicalSpace X›) ≤ _
          rw [induced_compose]
          exact le_rfl)
  refine ⟨hspec, ?_⟩
  unfold topologicalKrullDim Order.krullDim
  apply iSup_le
  intro c
  let F := TopologicalSpace.IrreducibleCloseds.map
    (Subtype.val : TopCat.puncturedGeneralizations Z → X) continuous_subtype_val
  have hF : StrictMono F :=
    TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing .subtypeVal
  obtain ⟨x, hx⟩ := c.head.isIrreducible.nonempty
  obtain ⟨z, hzx, hzZ⟩ := x.property.1
  let D : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure ({z} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  have hxF : x.val ∈ (F c.head : Set X) :=
    subset_closure ⟨x, hx, rfl⟩
  have hDZ : (D : Set X) ⊆ Z :=
    closure_minimal (Set.singleton_subset_iff.mpr hzZ) hZ
  have hDF : D < F c.head := by
    refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
    · exact closure_minimal
        (Set.singleton_subset_iff.mpr
          ((F c.head).isClosed.closure_subset_iff.mpr
            (Set.singleton_subset_iff.mpr hxF) hzx)) (F c.head).isClosed
    · intro h
      exact x.property.2 (hDZ (h hxF))
  let d := (c.map F hF).cons D (by simpa using hDF)
  have hd := (Order.LTSeries.length_le_krullDim d).trans hdim
  have hd' : c.length + 1 ≤ n := by
    simp only [d, RelSeries.cons_length, LTSeries.map_length] at hd
    exact_mod_cast hd
  have hc : c.length ≤ n - 1 := by omega
  exact_mod_cast hc

end Topology
