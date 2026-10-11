/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Closed points of affine opens in schemes locally of finite type over a field

Source: Stacks Project, Tag 0478, Lemma 33.14.1
(blueprint: lem-sc-affine-maximal-points-closed-in-lft-scheme).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A point closed in an affine open of a scheme locally of finite type over a field
is closed in the ambient scheme. Source: Stacks Project, Tag 0478
(blueprint: lem-sc-affine-maximal-points-closed-in-lft-scheme).

Proof: By `lem-sc-lft-over-field-jacobson-space`, the closed points of `X` in every
closed subset are dense in that subset. Let `Z` be the closure of the singleton of `x`
in `X`. Since `U` is open, its intersection with `Z` is the closure of the singleton
in `U`, hence is precisely that singleton by the hypothesis that `x` is closed in `U`
(`def-weil-affine-spectrum`, `def-weil-closed-points`). This intersection is a nonempty
open subset of `Z`. Density supplies a point closed in `X` in that intersection;
it must equal `x`. Thus `x` is closed in `X`. -/
theorem closedPoint_of_affineOpen {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (U : X.Opens) (_hU : IsAffineOpen U) (x : U) (hx : x ∈ closedPoints U) :
    (x : X) ∈ closedPoints X := by
  sorry

end AlgebraicGeometry
