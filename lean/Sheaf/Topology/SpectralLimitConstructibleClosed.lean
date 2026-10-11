/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.Constructions

/-!
# Quasi-compact limits of constructibly closed subsets

Source: Stacks Project, Topology, Tag 0A2V, parts (1) and (2)
(blueprint: lem-weil-pbc-spectral-limit-constructible-closed-quasi-compact).
-/

@[expose] public section

universe u v w

namespace Topology

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
    (hf_id : ∀ (i : I) (x : Y i), f i i le_rfl x = x)
    (hf_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : Y k),
      f i j hij (f j k hjk x) = f i k (le_trans hij hjk) x)
    {X : Type w} [tX : TopologicalSpace X] (p : ∀ i : I, X → Y i)
    (hp : ∀ i : I, Continuous (p i))
    (hp_compat : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ y : (∀ i : I, Y i),
      (∀ (i j : I) (h : i ≤ j), f i j h (y j) = y i) →
      ∃! x : X, ∀ i : I, p i x = y i)
    (htop : tX = ⨅ i : I, TopologicalSpace.induced (p i) (tY i))
    (Z : ∀ i : I, Set (Y i))
    (hZ : ∀ i : I, IsClosed[constructibleTopology (Y i)] (Z i))
    (hZ_compat : ∀ (i j : I) (h : i ≤ j), f i j h '' Z j ⊆ Z i) :
    IsCompact {x : X | ∀ i : I, p i x ∈ Z i} ∧ CompactSpace X := by
  sorry

end Topology
