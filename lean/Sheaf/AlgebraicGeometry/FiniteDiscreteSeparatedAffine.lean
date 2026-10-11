/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Affineness of a finite discrete separated scheme

Source: Stacks Project, Properties of Schemes, Lemma 28.10.6 (Tag 0CKV), final assertion
(blueprint: lem-sc-finite-discrete-separated-affine).
-/

universe u

open CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-compact scheme separated over `Spec ℤ` with finite discrete underlying space
is affine. Source: Stacks Project, Properties of Schemes, Lemma 28.10.6 (Tag 0CKV),
final assertion (blueprint: lem-sc-finite-discrete-separated-affine).

Proof: the finite discrete underlying space satisfies the hypotheses of
`lem-weil-pbc-finite-discrete-scheme-affine`, the Mathlib finite-discrete affineness
instance in `Mathlib.AlgebraicGeometry.Limits`. Apply that result to conclude `IsAffine Y`.
The quasi-compactness and separatedness assumptions are retained as in the node,
although the cited result does not need them. -/
theorem isAffine_of_finite_discrete_of_separated (Y : Scheme.{u}) [CompactSpace Y]
    [IsSeparated (terminal.from Y)] [Finite Y] [DiscreteTopology Y] : IsAffine Y := by
  sorry

end AlgebraicGeometry
