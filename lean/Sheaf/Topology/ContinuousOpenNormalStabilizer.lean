/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open normal stabilizers of continuous functions on profinite groups

Source: Stacks Project, etale-cohomology.tex, Tag 04JP,
definition-G-module-continuous; the profinite compactness argument is supplied in the DAG
(blueprint: lem-exc-coinduced-functions-open-stabilizer).
-/

universe u v

namespace ProfiniteGrp

/-- (blueprint: lem-exc-coinduced-functions-open-stabilizer) A continuous map from a profinite
group to a discrete space is invariant under right multiplication by some open normal subgroup.

Step 1: each fibre of `f` is open, and the fibres cover compact `G`. For every `x`, the
open-subgroup neighbourhood basis at one (from the finite discrete quotients of a profinite
group) gives an open subgroup `V x` with `x * V x` in the fibre of `f x`. A finite collection
of these cosets covers `G`; the intersection `V` of their subgroups is open and satisfies
`f (x * v) = f x` for all `x` and `v ∈ V`.

Step 2: an open subgroup of compact `G` has finite index. Intersecting the finitely many
conjugates of `V` over representatives of `G / V` gives an open normal subgroup `U ⊆ V`, and
the same right-invariance holds for `U`.

Source: Stacks Project, etale-cohomology.tex, Tag 04JP, with the group argument supplied in the DAG.
-/
theorem exists_openNormalSubgroup_right_invariant
    (G : ProfiniteGrp.{u}) (S : Type v) [TopologicalSpace S] [DiscreteTopology S]
    (f : G → S) (hf : Continuous f) :
    ∃ U : OpenNormalSubgroup G, ∀ x : G, ∀ a : G, a ∈ U → f (x * a) = f x := by
  sorry

end ProfiniteGrp
