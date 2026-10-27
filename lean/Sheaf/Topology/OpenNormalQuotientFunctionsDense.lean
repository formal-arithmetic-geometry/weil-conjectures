/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Separation.DisjointCover
import WeilConjectures.Topology.ContinuousOpenNormalStabilizer

/-!
# Density of functions on open normal quotients

Source: blueprint, `sec-six-functors-basics`, `sk-thm-sf-ctf-stability`, direct-images
proof, paragraph (3), auxiliary scalar tame-kernel input
(blueprint: lem-sfb-quotient-functions-dense).
The topological argument is supplied by the DAG proof, using Stacks Project, Topology,
Tag 0BR1 (`lemma-profinite-group`), and finite-map approximation in Mathlib.
-/

@[expose] public section

universe u v w

namespace ContinuousMap

/-- A compact Hausdorff group with an open normal subgroup basis is totally disconnected.
Every continuous map to a finite discrete space factors through an open normal quotient;
functions factoring through these quotients uniformly approximate every continuous function
with values in a normed field and form a dense subset for the supremum norm.

Source: blueprint, `sec-six-functors-basics`, `sk-thm-sf-ctf-stability`, direct-images
proof, paragraph (3), auxiliary scalar tame-kernel input; Stacks Project, Topology,
Tag 0BR1 (`lemma-profinite-group`)
(blueprint: lem-sfb-quotient-functions-dense).

Proof plan:
1. Every coset of an open subgroup is open, and its complement is the union of the other
   open cosets, so it is clopen. For distinct `x, y`, choose an open normal subgroup avoiding
   `x⁻¹ * y` using Hausdorffness and the given basis. Its coset through `x` separates `x` and
   `y`; hence any connected subset has at most one point.
2. Compactness gives a finite subcover of the disjoint open cosets of every open normal
   subgroup, so its quotient is finite. Its projection is continuous for the discrete
   topology, because preimages are unions of open cosets. Every function on the quotient
   therefore has continuous composite with the projection.
3. Regard the group as a profinite group by step 1. Apply
   `ProfiniteGrp.exists_openNormalSubgroup_right_invariant`
   (blueprint: lem-exc-coinduced-functions-open-stabilizer) to a continuous map to a finite
   discrete space. Right invariance makes its value on a coset well defined and gives the
   asserted quotient factorization.
4. For `f` and positive `ε`, apply
   `ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal`
   (blueprint: lem-sfb-profinite-finite-map-approximation) to the open neighbourhood
   `{(v, w) | ‖v - w‖ < ε / 2}` of the diagonal. Factor the resulting finite-valued map
   through an open normal quotient using step 3, and compose its quotient map with the
   finite approximation's value function. Step 2 makes this composite continuous.
   The pointwise bounds give supremum norm at most `ε / 2`, hence strictly less than `ε`.
   Every open norm ball thus meets the displayed set, which gives density. Completeness,
   nonarchimedean norms, countability and metrizability are not used. -/
theorem openNormalQuotientFunctions_dense
    (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] (B : Type v) [NormedField B]
    (h_basis : ∀ W : Set K, IsOpen W → (1 : K) ∈ W →
      ∃ U : OpenNormalSubgroup K, (U : Set K) ⊆ W) :
    TotallyDisconnectedSpace K ∧
      (∀ (F : Type w) [TopologicalSpace F] [DiscreteTopology F] [Finite F]
        (g : C(K, F)), ∃ (U : OpenNormalSubgroup K) (b : K ⧸ U.toSubgroup → F),
          ∀ x : K, g x = b (QuotientGroup.mk x)) ∧
      (∀ (f : C(K, B)) (ε : ℝ), 0 < ε →
        ∃ (U : OpenNormalSubgroup K) (b : K ⧸ U.toSubgroup → B) (d : C(K, B)),
          (∀ x : K, d x = b (QuotientGroup.mk x)) ∧ ‖f - d‖ < ε) ∧
      Dense {d : C(K, B) | ∃ (U : OpenNormalSubgroup K) (b : K ⧸ U.toSubgroup → B),
        ∀ x : K, d x = b (QuotientGroup.mk x)} := by
  sorry

end ContinuousMap
