module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order
import Sheaf.Topology.ClosedCoverPartitionProduct
import Sheaf.Topology.ClosedCoverSelectors

/-! # Closed-cover retractions and stabilizing selectors

Source: the scalar analytic expansion of paragraph (3) of
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, old steps 5–6.
This is an agent-formulated auxiliary lemma, not a theorem asserted by the blueprint.
(blueprint: lem-sfb-closed-cover-retractions-stabilizing-selectors)
-/

@[expose] public section

universe u

open Topology

namespace TopologicalSpace

/-- A countable nonempty closed cover has shrinking clopen partitions, retractions,
and locally constant selectors eventually equal to the first covering index.

The positive indices are literal positive naturals. `Finpartition` supplies finite,
pairwise disjoint, nonempty atoms covering the whole space. The membership equation
uniquely specifies the atom map `e`; its factors carry the discrete topology.
The union equation specifies `U`, and the two implications specify the least eligible
index and the default value of `k`. The final clause characterizes the least covering
index before asserting pointwise stabilization.

Source: scalar analytic expansion of paragraph (3), old steps 5–6, of the current
blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`.
(blueprint: lem-sfb-closed-cover-retractions-stabilizing-selectors)

Proof plan:
1. Use `isTopologicalBasis_isClopen` (lem-weil-pbc-profinite-clopen-basis) to choose
   clopen neighbourhoods inside balls of radius `2⁻ⁱ / 3`. Take a finite subcover at
   each level. Nonempty Boolean atoms of all covers through level `i` give refining
   partitions with diameter at most `2 * 2⁻ⁱ / 3 < 2⁻ⁱ`.
2. Coordinate cylinders pull back to clopen atoms, so the atom map is continuous.
   Equal coordinates put two points in the same arbitrarily small atoms, proving
   injectivity.
3. A sufficiently small atom about a point lies in any prescribed open neighbourhood;
   its coordinate cylinder proves continuity of the inverse onto the image.
4. For a point outside `e '' A j`, the coordinate disagreement opens cover `A j`.
   Compactness gives finitely many of them. The corresponding cylinder misses the
   image, proving it closed in the whole product. Nonemptiness is preserved by image.
5. Reindex the product by `i = n + 1`. Apply
   `PiNat.exists_retraction_subtype_of_isClosed`
   (lem-sfb-countable-discrete-product-closed-retraction) to `e '' A j`. Conjugate its
   restriction by the homeomorphism `A j ≃ₜ e '' A j` to obtain `ρ j` fixing `A j`.
6. The sets `U j i` are finite unions of clopen atoms. Refinement makes them decreasing.
   They contain `A j`; a small ball in the complement of the closed set excludes
   every point outside `A j` from some `U j i`, proving their intersection is `A j`.
7. Every membership test in the finite least-index rule is constant on each open
   atom. Thus the rule, including its default value one, is locally constant.
8. Fix a point and its least covering index `j₀`. Each of the finitely many smaller
   indices is eventually excluded by step 6. Beyond the maximum of those exclusion
   levels and `j₀`, precisely the least eligible index is `j₀`. When `j₀ = 1` the
   set of smaller indices is empty. No uniform bound, disjointness, or openness is used.
-/
theorem exists_closedCover_retractions_stabilizingSelectors
    (S : Type u) [MetricSpace S] [CompactSpace S] [TotallyDisconnectedSpace S]
    [Nonempty S] (A : ℕ+ → Set S) (hclosed : ∀ j, IsClosed (A j))
    (hnonempty : ∀ j, (A j).Nonempty) (hcover : (⋃ j, A j) = Set.univ) :
    ∃ P : ℕ+ → Finpartition (Set.univ : Set S),
      (∀ i, P (i + 1) ≤ P i) ∧
      (∀ i p, p ∈ (P i).parts → IsClopen p ∧ Metric.diam p < (1 / 2 : ℝ) ^ (i : ℕ)) ∧
      ∃ ρ : ∀ j, C(S, A j),
        (∀ j (a : A j), ρ j a = a) ∧
        ∃ e : S → ∀ i : ℕ+, WithDiscreteTopology (P i).parts,
          (∀ s i, s ∈ (e s i).ofTopology.val) ∧ IsEmbedding e ∧
          (∀ j, (e '' A j).Nonempty ∧ IsClosed (e '' A j)) ∧
          ∃ U : ℕ+ → ℕ+ → Set S,
            (∀ j i, U j i = ⋃ (p : (P i).parts) (_ : (p.val ∩ A j).Nonempty), p.val) ∧
            (∀ j i, IsClopen (U j i)) ∧
            (∀ j i, U j (i + 1) ⊆ U j i) ∧ (∀ j, (⋂ i, U j i) = A j) ∧
            ∃ k : ∀ i : ℕ+, LocallyConstant S {j : ℕ+ // j ≤ i},
              (∀ i s,
                ((∃ j : ℕ+, j ≤ i ∧ s ∈ U j i) →
                  s ∈ U (k i s).val i ∧
                    ∀ j : ℕ+, j ≤ i → s ∈ U j i → (k i s).val ≤ j) ∧
                ((∀ j : ℕ+, j ≤ i → s ∉ U j i) → (k i s).val = 1)) ∧
              ∀ s, ∃ j₀ : ℕ+,
                s ∈ A j₀ ∧ (∀ j : ℕ+, s ∈ A j → j₀ ≤ j) ∧
                ∃ i₀ : ℕ+, ∀ i : ℕ+, i₀ ≤ i → (k i s).val = j₀ := by
  obtain ⟨P, hrefine, hatoms, ρ, hρ, e, he, hemb, hclosedImage⟩ :=
    exists_closedCover_partitions_product S A hclosed hnonempty
  obtain ⟨U, hU, hUclopen, hUdec, hUinter, k, hk, hstab⟩ :=
    exists_closedCover_selectors S A hclosed hcover P
      (fun i p hp ↦ (hatoms i p hp).1) (fun i p hp ↦ (hatoms i p hp).2) hrefine
  exact ⟨P, hrefine, hatoms, ρ, hρ, e, he, hemb, hclosedImage,
    U, hU, hUclopen, hUdec, hUinter, k, hk, hstab⟩

end TopologicalSpace
