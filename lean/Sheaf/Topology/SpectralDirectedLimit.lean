/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Hom
import Mathlib.Order.Directed

/-!
# Directed inverse limits of spectral spaces

Source: Stacks Project, Topology, Tag 0A2Z, in the directed-set case
(blueprint: lem-weil-pbc-spectral-directed-limit-spectral).
-/

universe u v

namespace Topology

/-- A directed inverse limit of spectral spaces with spectral transition maps is spectral,
and its projections are spectral. Source: Stacks Project, Topology, Tag 0A2Z
(blueprint: lem-weil-pbc-spectral-directed-limit-spectral).

Proof:
1. The initial topology and directedness give a basis of inverse images of compact opens
from single stages. A common upper bound combines two such opens into a single inverse image.
2. For a compact open `U` at stage `i`, use the constructibly closed subsets
`f i j ⁻¹' U` for `i ≤ j` and the whole stage otherwise. The compatible-subset compactness
lemma `lem-weil-pbc-spectral-limit-constructible-closed-quasi-compact` (Tag 0A2V), with
`def-weil-pbc-constructible-topology`, makes their inverse limit `p i ⁻¹' U` compact.
The same lemma applied to whole stages makes the limit compact.
3. A compact open of the limit has a finite cover by these basic opens. Pass to a common
upper bound and take the finite union there to descend the compact open (Tag 0A2Y).
The empty open descends at any stage, using nonemptiness of the index.
4. Steps 1--3 give a basis of compact opens, compact intersections of compact opens,
and spectral projections. These are the compactness, prespectrality, and
quasi-separatedness clauses of `def-weil-spectral-space`.
5. For an irreducible closed subset `Z`, the closures of its images in the stages are
irreducible by `lem-weil-pbc-irreducible-continuous-image` and
`lem-weil-pbc-irreducible-closure`. Their unique generic points are compatible, hence lift
to a limit point. A basic-open neighbourhood argument shows that this point belongs to
`Z` and its closure equals `Z`.
6. Any other generic point maps to the same generic point at every stage. Injectivity of
the tuple map gives uniqueness. Thus the limit is sober, completing spectrality.
-/
theorem spectralSpace_directedLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Y : I → Type u) [∀ i : I, TopologicalSpace (Y i)] [∀ i : I, SpectralSpace (Y i)]
    (f : ∀ (i j : I), i ≤ j → Y j → Y i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hf_id : ∀ i : I, f i i le_rfl = id)
    (hf_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      f i j hij ∘ f j k hjk = f i k (le_trans hij hjk))
    (X : Type v) [tX : TopologicalSpace X] (p : ∀ i : I, X → Y i)
    (hp : ∀ i : I, Continuous (p i))
    (hp_compat : ∀ (i j : I) (h : i ≤ j), f i j h ∘ p j = p i)
    (hp_injective : Function.Injective (fun x : X => fun i : I => p i x))
    (hp_surjective : ∀ s : ∀ i : I, Y i,
      (∀ (i j : I) (h : i ≤ j), f i j h (s j) = s i) →
      ∃ x : X, ∀ i : I, p i x = s i)
    (h_initial : tX = ⨅ i : I, TopologicalSpace.induced (p i) inferInstance) :
    SpectralSpace X ∧ ∀ i : I, IsSpectralMap (p i) := by
  sorry

end Topology
