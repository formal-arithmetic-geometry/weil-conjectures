module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact

/-! # Finite rectangular quotients with small metric oscillation

Source: the agent-written topological auxiliary argument attached to paragraph (3) of
literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md; product compactness is Stacks Tag 08ZU.
The blueprint paragraph supplies application context, not this topological proof.
(blueprint: lem-sfb-profinite-product-finite-oscillation)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open Topology

namespace ContinuousMap

/-- A finite clopen partition of the parameter space and one open normal subgroup in
all group coordinates make the metric oscillation strictly smaller than ε.
The map p takes each point to its unique partition part. Its target is given the
discrete topology explicitly. The quotient has its canonical group structure and
quotient topology, which the conclusion asserts to be discrete.

Source: agent-written auxiliary argument for paragraph (3) of the current blueprint's
sk-thm-sf-ctf-stability-direct-images.proof.md; Stacks Tag 08ZU for product compactness
(blueprint: lem-sfb-profinite-product-finite-oscillation).

Proof:
1. For empty S use the empty partition and the whole group N = G; both canonical
   maps are continuous surjections, and the bound is vacuous.
2. Otherwise, around each x = (s,g), take the inverse image of the ε/2 ball about
   f(x). The product topology, clopen basis of S and open-normal identity basis of G
   give an open rectangle C_x × ∏ g_i H_{x,i} inside it.
3. By lem-weil-pbc-tychonoff-product-quasi-compact (Pi.compactSpace), the product is
   compact. Choose a finite subcover by these rectangles.
4. Refine their finitely many clopen parameter sets by their Boolean membership
   patterns, discarding empty atoms. These atoms form a finite clopen partition.
5. Intersect all the finitely many H_{x,i} to obtain one open normal subgroup N.
6. Points with the same parameter part and equal cosets modulo N belong to a common
   chosen rectangle. Two ε/2 bounds and the triangle inequality give the strict
   ε bound. No completeness of Y is used.
7. The unique-part map is onto because parts are nonempty; inverse images of sets
   of parts are unions of open parts. Normality gives the canonical quotient group
   and quotient homomorphism. Its open cosets cover compact G, so only finitely many
   distinct cosets occur; their openness makes the quotient discrete. The quotient
   homomorphism is onto and continuous. Its product with p has precisely the fibres
   described in step 6.
-/
theorem exists_finite_partition_openNormalSubgroup_small_oscillation
    (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (hS : TopologicalSpace.IsTopologicalBasis {U : Set S | IsClopen U})
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (hG : ∀ U ∈ nhds (1 : G), ∃ N : OpenNormalSubgroup G, (N : Set G) ⊆ U)
    (r : ℕ) (hr : 1 ≤ r) (Y : Type w) [MetricSpace Y]
    (f : C(S × (Fin r → G), Y)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Set (Set S)) (N : OpenNormalSubgroup G),
      P.Finite ∧ Setoid.IsPartition P ∧ (∀ U ∈ P, IsClopen U) ∧
      Finite (G ⧸ N.toSubgroup) ∧ DiscreteTopology (G ⧸ N.toSubgroup) ∧
      Continuous (QuotientGroup.mk' N.toSubgroup) ∧
      Function.Surjective (QuotientGroup.mk' N.toSubgroup) ∧
      ∃ p : S → P,
        (∀ s : S, s ∈ (p s).val) ∧
        @Continuous S P _ ⊥ p ∧ Function.Surjective p ∧
        ∀ (s s' : S) (g g' : Fin r → G), p s = p s' →
          (∀ i : Fin r, QuotientGroup.mk' N.toSubgroup (g i) =
            QuotientGroup.mk' N.toSubgroup (g' i)) →
          dist (f (s, g)) (f (s', g')) < ε := by
  sorry

end ContinuousMap
