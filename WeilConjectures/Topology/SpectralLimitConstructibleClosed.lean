/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.Constructions
import WeilConjectures.SixFunctors.ConstructibleTopologyHausdorff
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Hom
import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.WithTopology

/-!
# Quasi-compact limits of constructibly closed subsets

For an inverse system of spectral spaces, compatible constructibly closed subsets have a
quasi-compact limit.

## Implementation details

In the constructible topology each stage is compact Hausdorff and the transition maps are
continuous. The compatible families lying in the given subsets form a closed, hence compact,
subset of the product, and the limit is its continuous image.

## References

* [Stacks Project, Tags 0A2S and 0A2V](https://stacks.math.columbia.edu/tag/0A2V)
-/

@[expose] public section

universe u v w

/-- A spectral map of spectral spaces is continuous for their constructible topologies. -/
theorem IsSpectralMap.continuous_constructibleTopology
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [SpectralSpace X] [SpectralSpace Y] {f : X → Y} (hf : IsSpectralMap f) :
    @Continuous X Y (constructibleTopology X) (constructibleTopology Y) f := by
  rw [continuous_generateFrom_iff]
  intro s hs
  rcases hs with hs | hs
  · exact IsCompact.isOpen_constructibleTopology_of_isOpen
      (hf.isCompact_preimage_of_isOpen hs.1 hs.2)
      (hf.continuous.isOpen_preimage s hs.1)
  · apply IsCompact.isOpen_constructibleTopology_of_isClosed
    · rw [← Set.preimage_compl]
      exact hf.isCompact_preimage_of_isOpen hs.1.isOpen_compl hs.2
    · exact hs.1.preimage hf.continuous

namespace Topology

-- These diagram axioms are redundant for compactness; keep the existing interface.
/-- For an inverse system of spectral spaces indexed by any preorder, constructibly closed
compatible subsets have a quasi-compact limit, and the whole limit is quasi-compact. -/
theorem isCompact_limit_constructibleClosed
    {I : Type u} [Preorder I] (Y : I → Type v)
    [tY : ∀ i : I, TopologicalSpace (Y i)] [∀ i : I, SpectralSpace (Y i)]
    (f : ∀ (i j : I), i ≤ j → Y j → Y i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (_hf_id : ∀ (i : I) (x : Y i), f i i le_rfl x = x)
    (_hf_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : Y k),
      f i j hij (f j k hjk x) = f i k (le_trans hij hjk) x)
    {X : Type w} [tX : TopologicalSpace X] (p : ∀ i : I, X → Y i)
    (_hp : ∀ i : I, Continuous (p i))
    (hp_compat : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ y : (∀ i : I, Y i),
      (∀ (i j : I) (h : i ≤ j), f i j h (y j) = y i) →
      ∃! x : X, ∀ i : I, p i x = y i)
    (htop : tX = ⨅ i : I, TopologicalSpace.induced (p i) (tY i))
    (Z : ∀ i : I, Set (Y i))
    (hZ : ∀ i : I, IsClosed[constructibleTopology (Y i)] (Z i))
    (_hZ_compat : ∀ (i j : I) (h : i ≤ j), f i j h '' Z j ⊆ Z i) :
    IsCompact {x : X | ∀ i : I, p i x ∈ Z i} ∧ CompactSpace X := by
  classical
  let cY : ∀ i : I, TopologicalSpace (Y i) := fun i ↦ constructibleTopology (Y i)
  let : ∀ i : I, TopologicalSpace (Y i) := tY
  have hc : ∀ i : I, @CompactSpace (Y i) (cY i) := by
    intro i
    exact @Function.Surjective.compactSpace (WithConstructibleTopology (Y i)) (Y i)
      _ (cY i) _ (WithTopology.continuous_ofTopology _) inferInstance
      (WithTopology.ofTopology_surjective _)
  have ht : ∀ i : I, @T2Space (Y i) (cY i) := fun i ↦
    t2Space_constructibleTopology (Y i)
  have hf' : ∀ (i j : I) (h : i ≤ j),
      @Continuous (Y j) (Y i) (cY j) (cY i) (f i j h) := fun i j h ↦
    (hf i j h).continuous_constructibleTopology
  have hid : ∀ i : I, @Continuous (Y i) (Y i) (cY i) (tY i) id := by
    intro i
    exact continuous_id_of_le constructibleTopology_le
  let : ∀ i : I, TopologicalSpace (Y i) := cY
  let : ∀ i : I, CompactSpace (Y i) := hc
  let : ∀ i : I, T2Space (Y i) := ht
  let L : Set (∀ i : I, Y i) :=
    {y | ∀ (i j : I) (h : i ≤ j), f i j h (y j) = y i}
  have hL : IsClosed L := by
    simp only [L, Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun h ↦
      isClosed_eq ((hf' i j h).comp (continuous_apply j)) (continuous_apply i)
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL.isCompact
  let realize : L → X := fun y ↦ (hlimit y.val y.property).choose
  have hrealize_spec (y : L) (i : I) : p i (realize y) = y.val i :=
    (hlimit y.val y.property).choose_spec.1 i
  have hrealize : Continuous realize := by
    rw [htop, continuous_iInf_rng]
    intro i
    rw [continuous_induced_rng]
    have heq : p i ∘ realize = fun y : L ↦ y.val i :=
      funext fun y ↦ hrealize_spec y i
    rw [heq]
    exact @Continuous.comp L (Y i) (Y i) _ (cY i) (tY i)
      (fun y : L ↦ y.val i) id (hid i)
      ((continuous_apply i).comp continuous_subtype_val)
  have hrealize_surj : Function.Surjective realize := by
    intro x
    let y : L := ⟨fun i ↦ p i x, fun i j h ↦ hp_compat i j h x⟩
    refine ⟨y, ?_⟩
    exact ((hlimit y.val y.property).choose_spec.2 x (fun _ ↦ rfl)).symm
  have hclosed : IsClosed {y : L | ∀ i : I, y.val i ∈ Z i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦
      (hZ i).preimage ((continuous_apply i).comp continuous_subtype_val)
  have himage : realize '' {y : L | ∀ i : I, y.val i ∈ Z i} =
      {x : X | ∀ i : I, p i x ∈ Z i} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      rw [hrealize_spec]
      exact hy i
    · intro hx
      obtain ⟨y, rfl⟩ := hrealize_surj x
      refine ⟨y, ?_, rfl⟩
      intro i
      rw [← hrealize_spec]
      exact hx i
  exact ⟨himage ▸ hclosed.isCompact.image hrealize,
    Function.Surjective.compactSpace hrealize hrealize_surj⟩

end Topology
