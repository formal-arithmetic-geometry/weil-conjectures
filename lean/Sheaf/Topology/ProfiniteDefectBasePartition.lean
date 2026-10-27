module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Setoid.Partition
public import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Compactness.Compact

/-! # A finite clopen base partition annihilating a discrete defect

Source: Stacks Project, topology.tex, Tags 08ZY and 08ZZ, for finite clopen partitions;
agent-formulated compact nonzero-locus argument in lem-sfb-finite-valued-cech-cocycle-descent,
old steps 4--5 (blueprint: lem-sfb-profinite-defect-base-partition).
This auxiliary assertion is not a standalone assertion of either Stacks tag.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace ContinuousMap

/-- A continuous discrete defect that vanishes on equal-image tuples vanishes on all
source tuples whose images lie in one block of a suitable finite clopen base partition.
`Setoid.IsPartition` excludes empty blocks and gives a unique block through each point;
thus its blocks are pairwise disjoint and cover the base, including an empty partition
when the base is empty. No surjectivity of q is required.

Source: Stacks Project, topology.tex, Tags 08ZY and 08ZZ, and the agent-formulated
compact defect argument in lem-sfb-finite-valued-cech-cocycle-descent, old steps 4--5
(blueprint: lem-sfb-profinite-defect-base-partition).

Proof:
1. Let K be the nonzero locus of e. Discreteness makes it closed. The product T^r
   is compact by Pi.compactSpace (lem-weil-pbc-tychonoff-product-quasi-compact),
   so K is compact by IsClosed.isCompact (lem-weil-pbc-closed-in-quasi-compact).
   The equal-image vanishing hypothesis says K contains no equal-image tuple.
2. For each x in K choose coordinates i,j with q(x_i) unequal to q(x_j).
   Hausdorffness and the clopen basis isTopologicalBasis_isClopen
   (lem-weil-pbc-profinite-clopen-basis) give a clopen C containing the first
   image and excluding the second. The condition q(t_i) in C and q(t_j) outside C
   defines an open neighbourhood W of x. Compactness gives finitely many such W
   covering K; keep their clopens C. If K is empty, keep no clopens.
3. Form all Boolean membership atoms of these finitely many clopens and discard
   the empty atoms. Finite intersections and complements make each atom clopen.
   Every base point has exactly one membership pattern, so the remaining atoms
   are a finite partition. When the base is empty the partition is empty.
4. If a tuple has all images in one atom but has nonzero e, it belongs to one
   selected W. Its two selected images then have opposite membership in the
   corresponding clopen C, contradicting that they lie in one atom. Hence e is zero.
   No base point was lifted along q. For r=1, the zero group, or empty T, K is empty;
   use the one-block partition of a nonempty base and the empty partition otherwise.
-/
theorem exists_finite_clopen_base_partition_of_eq_zero_on_equal_images
    (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T]
    [TotallyDisconnectedSpace T]
    (S : Type v) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [TotallyDisconnectedSpace S]
    (q : T → S) (hq : Continuous q) (r : ℕ) (hr : 1 ≤ r)
    (M : Type w) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (e : (Fin r → T) → M) (he : Continuous e)
    (hzero : ∀ t : Fin r → T, (∀ i j : Fin r, q (t i) = q (t j)) → e t = 0) :
    ∃ γ : Set (Set S), γ.Finite ∧ Setoid.IsPartition γ ∧
      (∀ B ∈ γ, IsClopen B) ∧
      ∀ B ∈ γ, ∀ t : Fin r → T, (∀ i : Fin r, q (t i) ∈ B) → e t = 0 := by
  sorry

end ContinuousMap
