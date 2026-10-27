/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Codimension one of an affine-open boundary

Source: Stacks Project, Divisors, Tag 0BCV, dense-open clause, using Tags 0BCU and 0BCR
(blueprint: lem-sfb-affine-open-boundary-codimension-one).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- The local ring at any generic point of a boundary component of a dense affine open
in a separated locally Noetherian scheme has Krull dimension one.
Source: Stacks Project, Divisors, Tag 0BCV, lemma-complement-affine-open, dense-open clause
(blueprint: lem-sfb-affine-open-boundary-codimension-one).

Proof:
1. The inclusion of U is affine by
   lem-weil-pbc-affine-source-separated-target-affine-morphism. Choose an affine
   neighbourhood V = Spec R of xi. By pqf-lem-affine-open-locnoeth, R is Noetherian;
   lem-weil-pbc-affine-open-stalk-localization identifies A = O_{X,xi} with R_p,
   so lem-weil-pbc-localization-noetherian makes A Noetherian and local.
2. By lem-weil-pbc-spec-local-ring-canonical-morphism the local spectrum maps to the
   generalizations of xi, sending its closed point to xi. The map is injective by
   lem-weil-pbc-localization-spectrum-embedding. If a generalization y of xi lies
   in the boundary, its closure contains Z and is irreducible in the boundary.
   Maximality of Z forces equality; lem-sc-scheme-sober then gives y = xi.
   Thus the pullback of U is exactly the punctured local spectrum, with its
   restricted structure sheaf (def-weil-open-immersion).
3. By lem-weil-pbc-affine-morphism-permanence this pullback is affine. Apply
   lem-sfb-affine-punctured-local-dimension to deduce dim A <= 1.
4. The affine neighbourhood V is Noetherian by pqf-def-locnoeth and
   lem-weil-pbc-affine-scheme-qcqs. By lem-weil-pbc-noetherian-finitely-many-components
   it has finitely many components C_i, with generic points eta_i by lem-sc-scheme-sober.
   The complement in V of all components other than C_i is a nonempty open inside C_i:
   otherwise irreducibility would put C_i in a distinct component. Density makes this
   open meet U, so eta_i lies in U. For a component containing xi, eta_i strictly
   generalizes xi. By lem-sc-scheme-stalk-dimension-generalization-chains, dim A >= 1.
   Combining the bounds gives equality. When U = X there are no boundary components. -/
theorem affine_open_boundary_codimension_one
    (X : Scheme.{u}) [X.IsSeparated] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U) (hDense : Dense (U : Set X))
    (Z : Set {x : X // x ∉ U})
    (hZ : Z ∈ irreducibleComponents {x : X // x ∉ U})
    (xi : X) (hxi : IsGenericPoint xi (Subtype.val '' Z)) :
    ringKrullDim (X.presheaf.stalk xi) = 1 := by
  sorry

end AlgebraicGeometry
