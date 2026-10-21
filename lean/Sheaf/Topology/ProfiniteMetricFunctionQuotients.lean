/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact

/-!
# Metrizable profinite quotients for one metric-valued function

Source: main-20261015 blueprint, `sec-six-functors-basics`, direct-images proof,
paragraph (3), scalar tame-kernel expansion
(blueprint: lem-sfb-profinite-metric-function-quotients).
The topological argument is an agent-formulated auxiliary lemma; an exact literature
reference remains WANTED in the DAG source. The blueprint paragraph motivates its application.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Profinite

/-- A continuous metric-valued function on `S × G^r` descends through simultaneous
metrizable profinite space and group quotients. Completeness of the target is not needed.
Source: main-20261015 blueprint, direct-images proof, paragraph (3), scalar tame-kernel
expansion (blueprint: lem-sfb-profinite-metric-function-quotients); agent-formulated
auxiliary lemma, exact literature reference WANTED.

Proof plan from the DAG:
1. If `S` is empty, take the empty quotient space and the trivial quotient group; the
   factorization and continuity assertions have empty domain, even when `Y` is empty.
2. The domain is compact by `lem-weil-pbc-tychonoff-product-quasi-compact`. For each positive
   epsilon, continuity gives clopen-by-coset rectangles of oscillation less than epsilon,
   using the clopen basis on `S` and the open normal subgroup basis on `G`.
3. Choose a finite rectangle cover. Boolean atoms of the parameter clopens and the
   intersection of the finitely many normal subgroups give uniform small oscillation
   on the common fibres, with the same subgroup in every group coordinate.
4. Repeat at epsilon `2^(-n)` to get finite discrete quotients `A_n` of `S` and finite
   discrete quotient groups `B_n` of `G`. All coordinate quotient maps are continuous
   surjections; the group maps are homomorphisms.
5. Take the images of the diagonal maps into the countable products of the `A_n` and `B_n`,
   with the subspace topology of `def-kun-subspace-topology`. By
   `lem-weil-pbc-continuous-image-quasi-compact` these images are compact. Cylinder sets
   separate points and give a clopen basis on the space image.
6. The group image is a subgroup with continuous operations. Finite intersections of
   coordinate kernels are open normal subgroups forming a neighbourhood basis at one.
7. Countably many coordinate maps to finite discrete metric spaces separate points.
   Apply `lem-sfb-compact-countable-separating-metrizable` to both compact images.
8. Two points in the same product quotient fibre have values at distance less than `2^(-n)`
   for every `n`. Their values are equal by metric separation, inside `Y` itself.
9. The product quotient map is continuous and surjective from a compact space to a Hausdorff
   space, hence is a quotient map by `lem-sfb-compact-hausdorff-surjection-quotient`.
10. Define the descended function by the common value on each fibre. The quotient-map
    criterion proves continuity. No completion is involved. Finite quotients, countable
    products and their image subsets stay in the universes of `def-weil-size-convention`.
-/
theorem exists_metrizable_quotients_factorization
    (S : Profinite.{u}) (G : ProfiniteGrp.{u}) (r : ℕ) (hr : 1 ≤ r)
    (Y : Type v) [MetricSpace Y] (f : C(S × (Fin r → G), Y)) :
    ∃ (S₀ : Profinite.{u}) (G₀ : ProfiniteGrp.{u}),
      TopologicalSpace.MetrizableSpace S₀ ∧ TopologicalSpace.MetrizableSpace G₀ ∧
      ∃ (p : C(S, S₀)) (q : G →ₜ* G₀) (f₀ : C(S₀ × (Fin r → G₀), Y)),
        Function.Surjective p ∧ Function.Surjective q ∧
        ∀ x : S × (Fin r → G), f x = f₀ (p x.1, fun i : Fin r => q (x.2 i)) := by
  sorry

end Profinite
