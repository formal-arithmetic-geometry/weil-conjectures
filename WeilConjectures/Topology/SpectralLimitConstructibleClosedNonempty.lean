/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.Spectral.Hom
import WeilConjectures.Topology.Spectral.ConstructibleTopologyHausdorff
import WeilConjectures.Topology.SpectralMapConstructibleContinuous

/-!
# Compatible points in constructibly closed subsets of spectral spaces

Source: literature/stacks-project/topology.tex, Topology, Lemma Tag 0A2W
(blueprint: lem-weil-pbc-spectral-limit-constructible-closed-nonempty)
-/

@[expose] public section

universe u

open Set Topology

/-- A spectral space is compact in its constructible topology. -/
theorem compactSpace_constructibleTopology (X : Type*) [TopologicalSpace X] [SpectralSpace X] :
    @CompactSpace X (constructibleTopology X) :=
  @Function.Surjective.compactSpace _ _ _ (constructibleTopology X) _
    (WithTopology.continuous_ofTopology _) _ (WithTopology.ofTopology_surjective _)

/-- An inverse system of Hausdorff spaces indexed by a directed preorder, together with a
compatible family of nonempty compact subsets, has a compatible point lying in these subsets. -/
theorem exists_compatible_point_of_isCompact
    {K : Type*} [Preorder K] [Nonempty K] [IsDirected K (fun k k' => k ≤ k')]
    (Y : K → Type*) [tY : ∀ k, TopologicalSpace (Y k)] [hT2 : ∀ k, T2Space (Y k)]
    (g : ∀ k k', k ≤ k' → Y k' → Y k)
    (hg : ∀ k k' (h : k ≤ k'), Continuous (g k k' h))
    (hcomp : ∀ k k' k'' (h : k ≤ k') (h' : k' ≤ k'') (x : Y k''),
      g k k' h (g k' k'' h' x) = g k k'' (le_trans h h') x)
    (Z : ∀ k, Set (Y k)) (hZne : ∀ k, (Z k).Nonempty) (hZc : ∀ k, IsCompact (Z k))
    (hZmap : ∀ k k' (h : k ≤ k'), Set.MapsTo (g k k' h) (Z k') (Z k)) :
    ∃ z : ∀ k, Y k, (∀ k, z k ∈ Z k) ∧
      ∀ k k' (h : k ≤ k'), g k k' h (z k') = z k := by
  classical
  let S : K → Set (∀ k, Y k) := fun k₀ =>
    (⋂ k, (fun z : ∀ k, Y k => z k) ⁻¹' Z k) ∩
      ⋂ k, ⋂ k', ⋂ (h : k ≤ k'), ⋂ (_ : k' ≤ k₀), {z | g k k' h (z k') = z k}
  have hS_closed : ∀ k₀, IsClosed (S k₀) := fun k₀ =>
    (isClosed_iInter fun k => (hZc k).isClosed.preimage (continuous_apply k)).inter
      (isClosed_iInter fun k => isClosed_iInter fun k' => isClosed_iInter fun h =>
        isClosed_iInter fun _ =>
          isClosed_eq ((hg k k' h).comp (continuous_apply k')) (continuous_apply k))
  have hS_compact : ∀ k₀, IsCompact (S k₀) := fun k₀ =>
    (isCompact_univ_pi hZc).of_isClosed_subset (hS_closed k₀) fun z hz =>
      fun k _ => (Set.mem_iInter.mp hz.1 k : _)
  have hS_mono : ∀ {k₀ k₁ : K}, k₀ ≤ k₁ → S k₁ ⊆ S k₀ := by
    intro k₀ k₁ h01 z hz
    refine ⟨hz.1, ?_⟩
    have h2 := hz.2
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at h2 ⊢
    exact fun k k' h hk' => h2 k k' h (hk'.trans h01)
  have hS_ne : ∀ k₀, (S k₀).Nonempty := by
    intro k₀
    obtain ⟨w, hw⟩ := hZne k₀
    refine ⟨fun k => if h : k ≤ k₀ then g k k₀ h w else (hZne k).some, ?_, ?_⟩
    · refine Set.mem_iInter.mpr fun k => ?_
      by_cases h : k ≤ k₀
      · simpa [h] using hZmap k k₀ h hw
      · simpa [h] using (hZne k).some_mem
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro k k' h hk'
      simp [hk', h.trans hk', hcomp]
  have hdir : Directed (· ⊇ ·) S := fun a b =>
    let ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a b
    ⟨c, hS_mono hac, hS_mono hbc⟩
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    S hdir hS_ne hS_compact hS_closed
  rw [Set.mem_iInter] at hz
  refine ⟨z, fun k => Set.mem_iInter.mp (hz k).1 k, fun k k' h => ?_⟩
  have h2 := (hz k').2
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at h2
  exact h2 k k' h le_rfl

/--
Source: literature/stacks-project/topology.tex, Topology, Lemma Tag 0A2W, part (1)
(blueprint: lem-weil-pbc-spectral-limit-constructible-closed-nonempty).
The proof constructs the constructible subspaces of the `Z k`, applies the
nonempty inverse-limit theorem for compact Hausdorff spaces, and reads the
resulting compatible family as points of the original subsets.
-/
theorem exists_compatible_point_of_spectral_constructible_closed
    {K : Type u} [Preorder K] [Nonempty K]
    [IsDirected K (fun k k' => k ≤ k')]
    (Y : K → Type u) [∀ k, TopologicalSpace (Y k)]
    [∀ k, SpectralSpace (Y k)]
    (g : ∀ k k', k ≤ k' → Y k' → Y k)
    (hg : ∀ k k' (h : k ≤ k'), IsSpectralMap (g k k' h))
    (hcomp : ∀ k k' k'' (h : k ≤ k') (h' : k' ≤ k''),
      (g k k' h) ∘ (g k' k'' h') = g k k'' (le_trans h h'))
    (Z : ∀ k, Set (Y k))
    (hZne : ∀ k, (Z k).Nonempty)
    (hZclosed : ∀ k, @IsClosed (Y k) (constructibleTopology (Y k)) (Z k))
    (hZmap : ∀ k k' (h : k ≤ k'), Set.MapsTo (g k k' h) (Z k') (Z k)) :
    ∃ z : ∀ k, Y k, (∀ k, z k ∈ Z k) ∧
      ∀ k k' (h : k ≤ k'), g k k' h (z k') = z k :=
  exists_compatible_point_of_isCompact (tY := fun k => constructibleTopology (Y k))
    (hT2 := fun k => t2Space_constructibleTopology (Y k)) Y g
    (fun k k' h => (hg k k' h).continuous_constructibleTopology)
    (fun k k' k'' h h' x => congrFun (hcomp k k' k'' h h') x) Z hZne
    (fun k => @IsClosed.isCompact _ (constructibleTopology (Y k))
      _ (compactSpace_constructibleTopology (Y k)) (hZclosed k)) hZmap
