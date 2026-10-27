module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Topology.DiscreteQuotient
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Compactness.Compact

/-! # Rectangular extension from a closed subspace of a profinite power

Source: Stacks Project, topology.tex, Tags 08ZY (lemma-profinite) and 08ZZ
(lemma-profinite-refine-open-covering); the agent-formulated rectangular refinement
argument of lem-sfb-finite-valued-cech-cocycle-descent, steps 2 and 3.
(blueprint: lem-sfb-profinite-rectangular-extension)

The blocks of `α : DiscreteQuotient T` are the fibers of `α.proj`. They are nonempty,
pairwise disjoint clopens covering `T`; compactness makes the block set finite.
For empty `T` the block set is empty. A tuple `a : Fin k → α` indexes the product
cell `{x | ∀ i, α.proj (x i) = a i}`. The same partition is used in every coordinate.
-/

@[expose] public section

universe u v

set_option autoImplicit false

namespace Topology

/-- A continuous finite discrete abelian-group-valued map on a closed subspace of
`T^k`, for positive `k`, extends continuously and is constant on the product cells
of one finite clopen partition of `T`, with value zero on cells disjoint from `K`.

Source: Stacks Project, topology.tex, Tags 08ZY (lemma-profinite) and 08ZZ
(lemma-profinite-refine-open-covering); agent-formulated auxiliary assertion in the
rectangular refinement argument of lem-sfb-finite-valued-cech-cocycle-descent.
(blueprint: lem-sfb-profinite-rectangular-extension)

Proof to be supplied in stage 3:
1. If T is empty, positivity of k makes its power and K empty. Use the empty
   partition and the unique map. If K is empty and T is nonempty, use the one-block
   partition and the zero map.
2. For each x in K, discreteness and continuity give an ambient open neighborhood
   on whose intersection with K the map c is constant. Choose a product open
   neighborhood inside it, and refine each coordinate to a clopen neighborhood
   using lem-weil-pbc-profinite-clopen-basis.
3. The resulting rectangles together with the complement of K cover the power.
   By lem-weil-pbc-tychonoff-product-quasi-compact the power is compact. Take a
   finite subcover; its selected rectangles cover K after discarding the complement.
4. Form the Boolean atoms of all coordinate clopens from these rectangles and
   discard empty atoms. This is one finite clopen partition of T.
5. A product cell meeting K lies inside any selected rectangle containing a point
   of that intersection, since each atom has constant membership in every selected
   coordinate clopen. Consequently c has one well-defined value on the intersection.
6. Assign that value to each cell meeting K and zero to every other cell. The cells
   partition the power, so this defines h, extends c, and has both stated cell properties.
7. Cells are open finite products of open blocks. The preimage of any open set is a
   union of cells, proving continuity. For the zero group every assigned value is zero.
-/
theorem profinite_rectangular_extension
    (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T]
    [TotallyDisconnectedSpace T] (k : ℕ) (hk : 1 ≤ k)
    (K : Set (Fin k → T)) (hK : IsClosed K)
    (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (c : C(K, M)) :
    ∃ (α : DiscreteQuotient T) (h : C((Fin k → T), M)),
      (∀ x : K, h x.val = c x) ∧
      (∀ x y : Fin k → T,
        (∀ i : Fin k, α.proj (x i) = α.proj (y i)) → h x = h y) ∧
      (∀ a : Fin k → α,
        Disjoint {x : Fin k → T | ∀ i : Fin k, α.proj (x i) = a i} K →
          ∀ x : Fin k → T, (∀ i : Fin k, α.proj (x i) = a i) → h x = 0) := by
  sorry

end Topology
