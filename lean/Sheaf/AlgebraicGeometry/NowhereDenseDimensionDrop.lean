/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.GDelta.Basic

/-!
# Dimension drop for nowhere-dense closed subsets

Source: Stacks Project, Tag 02P2, the nowhere-dense closed support and the finite-dimensional
Noetherian dimension argument (blueprint: lem-sc-hilbert-nowhere-dense-dimension-drop).
-/

universe u

namespace AlgebraicGeometry

/-- A nowhere-dense closed subset of a nonempty locally Noetherian scheme of finite
Krull dimension `d` has Krull dimension strictly less than `d`.
Source: Stacks Project, Tag 02P2, dimension argument for the nowhere-dense closed support
(blueprint: lem-sc-hilbert-nowhere-dense-dimension-drop).

Proof:
1. If `Z` is empty, its dimension is bottom and the assertion follows. Otherwise each
irreducible component `C` of `Z` lies in an irreducible component `W` of `X`, by
`lem-sc-irreducible-components-cover` (Stacks, Tag 004W).
2. The components of `X` are locally finite by `lem-sc-locnoeth-components-locally-finite`.
Near the generic point of `W`, remove the other components to obtain a nonempty open
subset of `X` contained in `W`. Thus `C = W` would contradict nowhere density of `Z`.
Consequently `C` is strictly contained in `W`, and every chain in `C` extends by `W`.
Its length plus one is therefore at most `dim W`, which is at most `d`.
3. Taking the supremum over the components of `Z`, using
`def-kun-topological-krull-dimension`, gives `dim Z ≤ d - 1` when `d` is positive.
For `d = 0`, a nonempty component would give a strict chain in `X`, a contradiction;
therefore `Z` is empty and again has dimension bottom.
-/
theorem Scheme.topologicalKrullDim_lt_of_isNowhereDense
    (X : Scheme.{u}) [Nonempty X] [IsLocallyNoetherian X]
    (d : ℕ) (hX : topologicalKrullDim X = (d : WithBot ℕ∞))
    (Z : Set X) (hZ : IsClosed Z) (hnow : IsNowhereDense Z) :
    topologicalKrullDim Z < (d : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
