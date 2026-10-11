/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Zero-dimensional schemes of finite type over a field

Source: Stacks Project, Varieties, Lemma 33.20.2 (Tag 06LH), algebraic case
(blueprint: lem-pc-algebraic-dim-zero-affine-finite).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme of finite type over a field and of dimension at most zero is affine, and its
structure morphism is finite (Stacks, Tag 06LH).
(blueprint: lem-pc-algebraic-dim-zero-affine-finite)

Proof: By the equality of `Scheme.dim` with topological Krull dimension
(`lem-pc-scheme-dimension-local-rings`), the topological dimension is at most zero. Finite type
then makes the underlying space finite and discrete
(`lem-weil-pbc-finite-type-dim-zero-artinian`). Such a scheme is affine
(`lem-weil-pbc-finite-discrete-scheme-affine`), say `Y = Spec B`. The algebra `B` is of finite
type over `k` (`lem-pc-affine-finite-type-algebra`). The one-member affine cover gives
`ringKrullDim B = dim Y ≤ 0` (`lem-pc-dimension-affine-open-cover`), so every prime of `B` is
maximal; this also covers the empty scheme, for which `B = 0`. The finite-type algebra `B` is
therefore finite-dimensional over `k` (`lem-weil-pbc-finite-type-algebra-dim-zero-finite`),
making the structure morphism finite. -/
theorem isAffine_and_isFinite_of_dim_le_zero {k : Type u} [Field k]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (hY : Y.dim ≤ 0) : IsAffine Y ∧ IsFinite (Y ↘ Spec (.of k)) := by
  sorry

end AlgebraicGeometry
