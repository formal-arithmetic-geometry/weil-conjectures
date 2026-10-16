/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.Topology.SpectralSpace.WLocal.ClosedPoints
public import WeilConjectures.Mathlib.Topology.Separation.Basic

/-!
# Clopen partitions of w-local spaces

We prove blueprint `lem-weil-pbc-w-local-partition`:

* the patch (constructible) topology of `Spec A` is compact Hausdorff
  (`PrimeSpectrum.t2Space_withConstructibleTopology`);
* the closed points of a w-local space form a profinite space;
* restriction to the closed points identifies clopen subsets of a w-local space `X` with clopen
  subsets of `X^c` (`WLocalSpace.existsUnique_isClopen_preimage_eq`), hence identifies clopen
  partitions;
* an open subset containing the closed points of a clopen subset contains the whole clopen subset
  (`WLocalSpace.subset_of_isOpen_of_closedPoints_subset`).
-/

@[expose] public section

open Topology

/-- The patch (constructible) topology of the prime spectrum of a ring is Hausdorff. Together with
`compactSpace_withConstructibleTopology`, the patch topology of `Spec A` is compact Hausdorff. -/
instance PrimeSpectrum.t2Space_withConstructibleTopology (A : Type*) [CommSemiring A] :
    T2Space (WithConstructibleTopology (PrimeSpectrum A)) := by
  rw [t2Space_iff]
  rintro ⟨p⟩ ⟨q⟩ hpq
  have hpq' : p ≠ q := fun h ↦ hpq (by rw [h])
  -- Distinct primes are separated by some `f`, which lies in one of them but not the other.
  have key : ∀ p q : PrimeSpectrum A, ∀ f : A, f ∈ p.asIdeal → f ∉ q.asIdeal →
      ∃ U V : Set (PrimeSpectrum A), IsOpen[constructibleTopology (PrimeSpectrum A)] U ∧
        IsOpen[constructibleTopology (PrimeSpectrum A)] V ∧ p ∈ U ∧ q ∈ V ∧ Disjoint U V := by
    intro p q f hfp hfq
    have hD : IsOpen[constructibleTopology (PrimeSpectrum A)]
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) :=
      TopologicalSpace.GenerateOpen.basic _
        (Or.inl ⟨(PrimeSpectrum.basicOpen f).2, PrimeSpectrum.isCompact_basicOpen f⟩)
    have hV : IsOpen[constructibleTopology (PrimeSpectrum A)]
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A))ᶜ :=
      TopologicalSpace.GenerateOpen.basic _
        (Or.inr ⟨(PrimeSpectrum.basicOpen f).2.isClosed_compl, by
          rw [compl_compl]; exact PrimeSpectrum.isCompact_basicOpen f⟩)
    exact ⟨_, _, hV, hD, fun h ↦ h hfp, hfq, disjoint_compl_left⟩
  obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ : ∃ U V : Set (PrimeSpectrum A),
      IsOpen[constructibleTopology (PrimeSpectrum A)] U ∧
      IsOpen[constructibleTopology (PrimeSpectrum A)] V ∧ p ∈ U ∧ q ∈ V ∧ Disjoint U V := by
    by_cases h : p.asIdeal ≤ q.asIdeal
    · have : ¬ q.asIdeal ≤ p.asIdeal := fun h' ↦ hpq' (PrimeSpectrum.ext (le_antisymm h h'))
      obtain ⟨f, hfq, hfp⟩ := Set.not_subset.mp this
      obtain ⟨U, V, hU, hV, hqU, hpV, hUV⟩ := key q p f hfq hfp
      exact ⟨V, U, hV, hU, hpV, hqU, hUV.symm⟩
    · obtain ⟨f, hfp, hfq⟩ := Set.not_subset.mp h
      exact key p q f hfp hfq
  exact ⟨WithTopology.ofTopology ⁻¹' U, WithTopology.ofTopology ⁻¹' V, hU, hV, hpU, hqV,
    hUV.preimage _⟩

namespace WLocalSpace

variable {X : Type*} [TopologicalSpace X] [WLocalSpace X]

instance t2Space_closedPoints : T2Space (closedPoints X) := inferInstance

instance totallyDisconnectedSpace_closedPoints : TotallyDisconnectedSpace (closedPoints X) :=
  inferInstance

/-- Two clopen subsets of a w-local space agreeing on the closed points agree. -/
lemma eq_of_isClopen_of_inter_closedPoints_eq {U V : Set X} (hU : IsClopen U) (hV : IsClopen V)
    (h : U ∩ closedPoints X = V ∩ closedPoints X) : U = V := by
  have key : ∀ {U V : Set X}, IsClopen U → IsClopen V →
      U ∩ closedPoints X = V ∩ closedPoints X → U ⊆ V := by
    intro U V hU hV h x hx
    obtain ⟨c, hc, hxc⟩ := exists_isClosed_specializes x
    have hcU : c ∈ U := hxc.mem_closed hU.isClosed hx
    have hcV : c ∈ V := (h ▸ ⟨hcU, mem_closedPoints_iff.mpr hc⟩ : c ∈ V ∩ closedPoints X).1
    exact hxc.mem_open hV.isOpen hcV
  exact (key hU hV h).antisymm (key hV hU h.symm)

/-- **Blueprint `lem-weil-pbc-w-local-partition`** (clopen subsets): every clopen subset of the
closed points of a w-local space extends uniquely to a clopen subset of the whole space. In
particular clopen partitions of `X` and of `X^c` correspond. -/
theorem existsUnique_isClopen_preimage_eq {C : Set (closedPoints X)} (hC : IsClopen C) :
    ∃! U : Set X, IsClopen U ∧ Subtype.val ⁻¹' U = C := by
  have hce : IsClosedEmbedding ((↑) : closedPoints X → X) :=
    IsClosed.isClosedEmbedding_subtypeVal WLocalSpace.isClosed_closedPoints
  let U := generalizationHull (Subtype.val '' C)
  let V := generalizationHull (Subtype.val '' Cᶜ)
  have hU_closed : IsClosed U :=
    isClosed_generalizationHull_of_wLocalSpace (hce.isClosedMap C hC.1)
  have hV_closed : IsClosed V :=
    isClosed_generalizationHull_of_wLocalSpace (hce.isClosedMap Cᶜ hC.compl.1)
  have hmem : ∀ z : X, z ∈ U ↔ ∃ c : closedPoints X, c ∈ C ∧ z ⤳ c := by
    intro z
    simp only [U, mem_generalizationHull_iff, Set.mem_image]
    exact ⟨fun ⟨_, ⟨c, hc, rfl⟩, h⟩ ↦ ⟨c, hc, h⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, ⟨c, hc, rfl⟩, h⟩⟩
  have hmemV : ∀ z : X, z ∈ V ↔ ∃ c : closedPoints X, c ∉ C ∧ z ⤳ c := by
    intro z
    simp only [V, mem_generalizationHull_iff, Set.mem_image, Set.mem_compl_iff]
    exact ⟨fun ⟨_, ⟨c, hc, rfl⟩, h⟩ ↦ ⟨c, hc, h⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, ⟨c, hc, rfl⟩, h⟩⟩
  have hUV : Uᶜ = V := by
    ext z
    rw [Set.mem_compl_iff, hmem, hmemV]
    obtain ⟨c, hc, hzc⟩ := exists_isClosed_specializes z
    constructor
    · intro h
      exact ⟨⟨c, mem_closedPoints_iff.mpr hc⟩, fun hC' ↦ h ⟨_, hC', hzc⟩, hzc⟩
    · rintro ⟨d, hd, hzd⟩ ⟨d', hd', hzd'⟩
      have := WLocalSpace.eq_of_specializes (mem_closedPoints_iff.mp d.2)
        (mem_closedPoints_iff.mp d'.2) hzd hzd'
      exact hd (Subtype.ext this ▸ hd')
  have hUclopen : IsClopen U := ⟨hU_closed, by rw [← isClosed_compl_iff, hUV]; exact hV_closed⟩
  have hpre : Subtype.val ⁻¹' U = C := by
    ext x
    rw [Set.mem_preimage, hmem]
    constructor
    · rintro ⟨c, hc, hxc⟩
      have : (c : X) = x := hxc.mem_closed (mem_closedPoints_iff.mp x.2) (Set.mem_singleton _)
      exact (Subtype.ext this : c = x) ▸ hc
    · exact fun hx ↦ ⟨x, hx, specializes_rfl⟩
  refine ⟨U, ⟨hUclopen, hpre⟩, fun U' ⟨hU', hpre'⟩ ↦ ?_⟩
  refine eq_of_isClopen_of_inter_closedPoints_eq hU' hUclopen ?_
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨hx, hxc⟩
    refine ⟨?_, hxc⟩
    have : (⟨x, hxc⟩ : closedPoints X) ∈ Subtype.val ⁻¹' U := by
      rw [hpre, ← hpre']; exact hx
    exact this
  · rintro ⟨hx, hxc⟩
    refine ⟨?_, hxc⟩
    have : (⟨x, hxc⟩ : closedPoints X) ∈ Subtype.val ⁻¹' U' := by
      rw [hpre', ← hpre]; exact hx
    exact this

/-- **Blueprint `lem-weil-pbc-w-local-partition`** (last part): an open subset containing the
closed points of a clopen subset `V` of a w-local space contains `V`, i.e. the corresponding
connected components. -/
lemma subset_of_isOpen_of_closedPoints_subset {U V : Set X} (hU : IsOpen U) (hV : IsClopen V)
    (h : V ∩ closedPoints X ⊆ U) : V ⊆ U := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := exists_isClosed_specializes x
  exact hxc.mem_open hU (h ⟨hxc.mem_closed hV.isClosed hx, mem_closedPoints_iff.mpr hc⟩)

/-- **Blueprint `lem-weil-pbc-w-local-partition`** (bundled form, for an affine w-local scheme
`Spec A`): the patch topology of `Spec A` is compact Hausdorff; the closed points form a profinite
space; clopen subsets of the closed points extend uniquely to clopen subsets of `Spec A`; and an
open subset containing the closed points of a clopen subset contains the clopen subset. -/
theorem partition_spec (A : Type*) [CommRing A] [WLocalSpace (PrimeSpectrum A)] :
    (CompactSpace (WithConstructibleTopology (PrimeSpectrum A)) ∧
      T2Space (WithConstructibleTopology (PrimeSpectrum A))) ∧
    (CompactSpace (closedPoints (PrimeSpectrum A)) ∧ T2Space (closedPoints (PrimeSpectrum A)) ∧
      TotallyDisconnectedSpace (closedPoints (PrimeSpectrum A))) ∧
    (∀ C : Set (closedPoints (PrimeSpectrum A)), IsClopen C →
      ∃! U : Set (PrimeSpectrum A), IsClopen U ∧ Subtype.val ⁻¹' U = C) ∧
    (∀ U V : Set (PrimeSpectrum A), IsOpen U → IsClopen V →
      V ∩ closedPoints (PrimeSpectrum A) ⊆ U → V ⊆ U) :=
  ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance, inferInstance⟩,
    fun _ hC ↦ existsUnique_isClopen_preimage_eq hC,
    fun _ _ hU hV h ↦ subset_of_isOpen_of_closedPoints_subset hU hV h⟩

end WLocalSpace
