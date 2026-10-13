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
import WeilConjectures.Topology.Spectral.ConstructibleTopologyHausdorff
import WeilConjectures.Topology.SpectralMapConstructibleContinuous
import WeilConjectures.Topology.SpectralLimitConstructibleClosedNonempty
import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Quasi-compact limits of constructibly closed subsets

Source: Stacks Project, Topology, Tag 0A2V, parts (1) and (2)
(blueprint: lem-weil-pbc-spectral-limit-constructible-closed-quasi-compact).
-/

@[expose] public section

universe u v w

namespace Topology

/-- Let `X` be the limit of an inverse system of Hausdorff spaces `Y i`, in the sense that
compatible families are uniquely realized by points of `X`, and a map into `X` is continuous
as soon as all its projections are. Then for compact subsets `Z i`, the set of points of `X`
whose projections lie in every `Z i` is compact. -/
theorem isCompact_limit_of_t2
    {I : Type u} [Preorder I] (Y : I → Type v)
    [tC : ∀ i : I, TopologicalSpace (Y i)] [hT2 : ∀ i : I, T2Space (Y i)]
    (f : ∀ (i j : I), i ≤ j → Y j → Y i)
    (hf : ∀ (i j : I) (h : i ≤ j), Continuous (f i j h))
    {X : Type w} [TopologicalSpace X] (p : ∀ i : I, X → Y i)
    (hp_compat : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ y : (∀ i : I, Y i),
      (∀ (i j : I) (h : i ≤ j), f i j h (y j) = y i) →
      ∃! x : X, ∀ i : I, p i x = y i)
    (hcont : ∀ {T : Type (max u v)} [TopologicalSpace T] (φ : T → X),
      (∀ i : I, Continuous (p i ∘ φ)) → Continuous φ)
    (Z : ∀ i : I, Set (Y i)) (hZ : ∀ i : I, IsCompact (Z i)) :
    IsCompact {x : X | ∀ i : I, p i x ∈ Z i} := by
  let S : Set (∀ i : I, Y i) :=
    Set.pi Set.univ Z ∩ {y | ∀ (i j : I) (h : i ≤ j), f i j h (y j) = y i}
  have hS_closed : IsClosed S := by
    refine (isClosed_set_pi fun i _ => (hZ i).isClosed).inter ?_
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun h =>
      isClosed_eq ((hf i j h).comp (continuous_apply j)) (continuous_apply i)
  have : CompactSpace S := isCompact_iff_compactSpace.mp
    ((isCompact_univ_pi hZ).of_isClosed_subset hS_closed Set.inter_subset_left)
  let φ : S → X := fun y => (hlimit y.1 y.2.2).exists.choose
  have hφ : ∀ (y : S) (i : I), p i (φ y) = y.1 i := fun y =>
    (hlimit y.1 y.2.2).exists.choose_spec
  have hφc : Continuous φ := hcont φ fun i => by
    have : p i ∘ φ = fun y : S => y.1 i := funext fun y => hφ y i
    rw [this]
    exact (continuous_apply i).comp continuous_subtype_val
  convert isCompact_range hφc using 1
  ext x
  constructor
  · intro hx
    have hy : (fun i => p i x) ∈ S :=
      ⟨fun i _ => hx i, fun i j h => hp_compat i j h x⟩
    exact ⟨⟨_, hy⟩, (hlimit _ hy.2).unique (hφ ⟨_, hy⟩) fun _ => rfl⟩
  · rintro ⟨y, rfl⟩ i
    rw [hφ y i]
    exact y.2.1 i trivial

/-- For an inverse system of spectral spaces indexed by any preorder, constructibly closed
compatible subsets have a quasi-compact limit, and the whole limit is quasi-compact.
Source: Stacks Project, Topology, Tag 0A2V, parts (1) and (2)
(blueprint: lem-weil-pbc-spectral-limit-constructible-closed-quasi-compact).

Proof outline:
1. Equip each stage with its constructible topology (def-weil-pbc-constructible-topology).
   It is compact and Hausdorff by lem-weil-pbc-spectral-constructible-topology-quasi-compact
   and lem-weil-pbc-spectral-constructible-topology-hausdorff. The transition maps are
   continuous by lem-weil-pbc-spectral-map-constructible-continuous.
2. The identity from the constructible topology to the original topology is continuous:
   compact opens form a basis (def-weil-spectral-space) and are constructibly open.
3. The product of the constructible spaces is compact by
   lem-weil-pbc-tychonoff-product-quasi-compact.
4. Inside this product, families lying in every Z_i and satisfying every compatibility
   equation form a closed subset: coordinate inverse images of Z_i are closed, and the
   equations are closed equalizers by lem-weil-pbc-hausdorff-equalizer-closed.
5. This closed subset is compact by lem-weil-pbc-closed-in-quasi-compact.
6. Unique realization of compatible families gives a map from this subset to X whose
   image is exactly the set of points whose projections lie in all Z_i.
7. Each coordinate of this map is continuous by step 2. The initial topology of X gives
   its continuity by lem-weil-pbc-initial-topology-continuity.
8. Its image is compact by lem-weil-pbc-continuous-image-quasi-compact. Taking every Z_i
   to be the whole stage gives compactness of X as well. -/
theorem isCompact_limit_constructibleClosed
    {I : Type u} [Preorder I] (Y : I → Type v)
    [tY : ∀ i : I, TopologicalSpace (Y i)] [∀ i : I, SpectralSpace (Y i)]
    (f : ∀ (i j : I), i ≤ j → Y j → Y i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    {X : Type w} [tX : TopologicalSpace X] (p : ∀ i : I, X → Y i)
    (hp : ∀ i : I, Continuous (p i))
    (hp_compat : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ y : (∀ i : I, Y i),
      (∀ (i j : I) (h : i ≤ j), f i j h (y j) = y i) →
      ∃! x : X, ∀ i : I, p i x = y i)
    (htop : tX = ⨅ i : I, TopologicalSpace.induced (p i) (tY i))
    (Z : ∀ i : I, Set (Y i))
    (hZ : ∀ i : I, IsClosed[constructibleTopology (Y i)] (Z i)) :
    IsCompact {x : X | ∀ i : I, p i x ∈ Z i} ∧ CompactSpace X := by
  have key : ∀ Z' : ∀ i : I, Set (Y i),
      (∀ i : I, IsClosed[constructibleTopology (Y i)] (Z' i)) →
        IsCompact {x : X | ∀ i : I, p i x ∈ Z' i} := fun Z' hZ' =>
    isCompact_limit_of_t2 (tC := fun i => constructibleTopology (Y i)) Y
      (hT2 := fun i => t2Space_constructibleTopology (Y i)) f
      (fun i j h => (hf i j h).continuous_constructibleTopology) p hp_compat hlimit
      (fun φ hφ => by
        subst htop
        exact continuous_iInf_rng.2 fun i => continuous_induced_rng.2 <|
          continuous_le_rng constructibleTopology_le (hφ i)) Z'
      (fun i => @IsClosed.isCompact _ (constructibleTopology (Y i)) _
        (compactSpace_constructibleTopology (Y i)) (hZ' i))
  refine ⟨key Z hZ, isCompact_univ_iff.mp ?_⟩
  simpa using key (fun _ => Set.univ) fun i => @isClosed_univ _ (constructibleTopology (Y i))

end Topology
