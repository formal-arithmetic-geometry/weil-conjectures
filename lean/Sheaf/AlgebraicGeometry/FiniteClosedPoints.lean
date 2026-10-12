/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints

/-!
# Closed subsets consisting of closed points

Source: the blueprint of the Weil conjectures, chapter `sec-smooth-purity`, unit
`sk-prop-sf-kunneth-ordinary` (blueprint: lem-kun-finite-closed-subscheme);
Stacks Project, Morphisms of Schemes, Lemma 29.15.6 (Tag 01T6), and
Properties of Schemes, Lemma 28.5.7 (Tag 0BA8).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A closed subset of a scheme of finite type over a field, consisting entirely of closed
points, is finite (blueprint: lem-kun-finite-closed-subscheme).

Proof plan (Stacks Project, Morphisms Lemma 01T6 and Properties Lemma 0BA8):

1. Since `Spec K` is Noetherian and `f` is of finite type, apply
   `lem-weil-pbc-finite-type-over-noetherian` to obtain that `X` is Noetherian.
2. Apply `lem-sc-noetherian-closed-points-finite` to the closed subset `E`. Its
   closed-point hypothesis is exactly `hclosed`, so it concludes `E.Finite`. -/
theorem IsClosed.finite_of_finiteType_over_field_of_closed_points
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f] {E : Set X} (hE : IsClosed E)
    (hclosed : ∀ x ∈ E, IsClosed {x}) : E.Finite := by
  sorry

end AlgebraicGeometry
