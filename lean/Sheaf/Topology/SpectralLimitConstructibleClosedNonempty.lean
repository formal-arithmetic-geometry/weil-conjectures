import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Hom

/-!
# Compatible points in constructibly closed subsets of spectral spaces

Source: literature/stacks-project/topology.tex, Topology, Lemma Tag 0A2W
(blueprint: lem-weil-pbc-spectral-limit-constructible-closed-nonempty)
-/


universe u

open Set Topology

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
    (hgid : ∀ k, g k k (le_rfl) = id)
    (hcomp : ∀ k k' k'' (h : k ≤ k') (h' : k' ≤ k''),
      (g k k' h) ∘ (g k' k'' h') = g k k'' (le_trans h h'))
    (Z : ∀ k, Set (Y k))
    (hZne : ∀ k, (Z k).Nonempty)
    (hZclosed : ∀ k, @IsClosed (Y k) (constructibleTopology (Y k)) (Z k))
    (hZmap : ∀ k k' (h : k ≤ k'), Set.MapsTo (g k k' h) (Z k') (Z k)) :
    ∃ z : ∀ k, Y k, (∀ k, z k ∈ Z k) ∧
      ∀ k k' (h : k ≤ k'), g k k' h (z k') = z k := by
  sorry
