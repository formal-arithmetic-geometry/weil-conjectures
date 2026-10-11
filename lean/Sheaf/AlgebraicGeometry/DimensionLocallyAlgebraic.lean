/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension of an irreducible locally algebraic scheme

Source: Stacks Project, Varieties, Lemma 33.20.3, Tag 0A21, part (3)
(blueprint: lem-sc-dimension-locally-algebraic).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For an irreducible scheme locally of finite type over a field, every nonempty open subset
and every point have the dimension of the whole scheme. Source: Stacks Project, Varieties,
Lemma 33.20.3, Tag 0A21, part (3) (blueprint: lem-sc-dimension-locally-algebraic).

Proof:
1. Replace `X` by its reduction (`def-weil-pbc-scheme-reduction`). The reduction map is a closed
   immersion and a homeomorphism (`lem-weil-pbc-reduction-universal-homeomorphism`), so its
   source is reduced and irreducible, hence integral (`def-pc-integral-scheme`). The map is
   locally of finite type (`lem-weil-pbc-immersion-base-change-lft`), and composition preserves
   that property (`lem-weil-pbc-proper-fp-permanence`). All the dimensions in the statement
   are preserved by the homeomorphism (`lem-weil-pbc-homeomorphism-krull-dimension`).
2. Choose a nonempty affine open `W₀` using `lem-weil-pbc-affine-opens-basis`, and put
   `d = dim W₀`. Every nonempty affine open has dimension `d` by
   `lem-sc-integral-locally-algebraic-affine-opens-dimension`: a closed point in the intersection
   compares their dimensions with its local-ring dimension (Stacks 0478 and 00OS).
3. A nonempty open `U` contains a nonempty affine open `W` by
   `lem-weil-pbc-affine-opens-basis`. Thus `d = dim W ≤ dim U` by
   `lem-weil-pbc-open-subspace-dimension-monotone`.
4. By `lem-weil-pbc-dimension-supremum-local-dimensions`, `dim U` is the supremum of its
   dimensions at points. Each point of `U` has an affine neighbourhood `W` contained in `U`,
   by `lem-weil-pbc-affine-opens-basis`. Its dimension at the point is at most `dim W = d`
   by `def-kun-topological-dimension-at-point`; the subspace topologies agree. Hence `dim U ≤ d`.
5. The preceding inequalities give `dim U = d`; applying this to `U = X` gives `dim X = d`,
   proving the first assertion.
6. Every open neighbourhood of a point `x` is nonempty and therefore has dimension `dim X`.
   The minimum of these dimensions is `dim X`, giving the second assertion by
   `def-kun-dimension`. -/
theorem dimension_locally_algebraic {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [IrreducibleSpace X] :
    (∀ U : X.Opens, (U : Set X).Nonempty →
      topologicalKrullDim (U : Set X) = topologicalKrullDim X) ∧
    (∀ x : X, topologicalKrullDimAt x = topologicalKrullDim X) := by
  sorry

end AlgebraicGeometry
