/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R5
-/
module

public import Sheaf.AlgebraicGeometry.CenteredToricTowerLiftData

/-!
# Uniqueness of the centered identification between toric tower lifts

Source: ILO, Travaux de Gabber, Exposé VIII, 3.2.14--3.2.20, pp.105--106
(blueprint: lem-trf-centered-toric-tower-lift-identification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Monoscheme

/-- Two already supplied centered lifts have a unique centered identification.
No new lift, equivariance hypothesis on centers, or regularity hypothesis is required.

Source: ILO VIII 3.2.14--3.2.20, pp.105--106
(blueprint: lem-trf-centered-toric-tower-lift-identification).

Proof: induct through the ordered stages, fixing the base by L.base and L'.base.
The initial realization equation follows from their initial fields. Given the centered
identification at stage i, pull back the second monoid center to the first monoscheme.
By the pullback formula of toric_ideal_comparison, its ring ideal is the pullback of the
second ring ideal. The realization equation and both center fields identify this with
the first ring ideal. Injectivity of toric_ideal_comparison identifies the actual coherent
monoid centers. Over each affine chart their saturated blowups now have identical charts
P[I-a]^sat and localized overlaps. The base monoid isomorphism extends to these charts
by sending p/a^m to its image divided by the corresponding image of a. These extensions
and their inverses agree on overlaps and glue to an isomorphism at stage i+1. The chart
formulas are local monoid maps, induce the specified scheme comparisons, and commute
with the blowup arrows. The specified scheme comparison agrees with this realization:
both lie over the preceding comparison, and on the dense original component tori their
maps agree; the normalized blowup is separated over its base and its source is reduced.
For uniqueness, any centered identification induces, at each stage, the prescribed
scheme map (L.iso i).hom followed by (L'.iso i).inv. On a monoid chart a monomial map is
determined by its realized map, since distinct monomials are linearly independent over Q;
its map on points is determined by inverse images of monoid primes. Applying this on
chart refinements shows equality of the local sheafed-space maps and hence of the glued
maps. The hom maps determine the isomorphisms, and function extensionality identifies
the entire family. This also treats n=0, empty spaces and unit-center stages. -/
theorem existsUnique_centeredToricTowerIdentification {n : ℕ} {M : Fine.{u}}
    {T : NormalizedTower.{u} n} {e₀ : T.level 0 ≅ realization (ULift.{u} ℚ) M}
    (L L' : CenteredToricTowerLift M T e₀) :
    ∃! e : ∀ i : Fin (n + 1), (L.tower.level i).space ≅ (L'.tower.level i).space,
      L.IsCenteredIdentification L' e := by sorry

end AlgebraicGeometry.Monoscheme
