/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.RepresentationTheory.HomogeneousCochainEvaluationBijective
import WeilConjectures.RepresentationTheory.HomogeneousCochainEvaluationDifferential

/-!
# Homogeneous and inhomogeneous continuous cochains

For a profinite group `G` and a discrete representation `N` with open stabilizers, invariant
homogeneous continuous cochains are identified with locally constant inhomogeneous cochains,
compatibly with the differentials.

## References

* [Stacks Project, Tag 0DVG](https://stacks.math.columbia.edu/tag/0DVG)
-/

@[expose] public section

universe u s

open CategoryTheory

namespace Rep

/-- Invariant homogeneous continuous cochains have locally constant inhomogeneous
coordinates: there are additive equivalences `t n` with locally constant functions on `Gⁿ`
under which the homogeneous differential becomes the usual inhomogeneous differential. -/
theorem exists_homogeneousCochains_inhomogeneous_coordinates
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : TopRep.{max u s} ℤ G) [DiscreteTopology N.V]
    (hN : ∀ x : N.V, IsOpen {g : G | N.ρ g x = x}) :
    ∃ t : ∀ n : ℕ, (TopRep.homogeneousCochains N).X n ≃+
        LocallyConstant (Fin n → G) N.V,
      ∀ (n : ℕ) (x : (TopRep.homogeneousCochains N).X n) (g : Fin (n + 1) → G),
        t (n + 1) (((TopRep.homogeneousCochains N).d n (n + 1)).hom x) g =
          N.ρ (g 0) (t n x (fun k ↦ g k.succ)) +
            ∑ k : Fin (n + 1),
              (-1 : ℤ) ^ (k.val + 1) • t n x (Fin.contractNth k (· * ·) g) := by
  let t (n : ℕ) := AddEquiv.ofBijective (homogeneousCochainEvaluation N n)
    (homogeneousCochainEvaluation_bijective N hN n)
  refine ⟨t, ?_⟩
  intro n x g
  exact homogeneousCochainEvaluation_differential N n x g

end Rep
