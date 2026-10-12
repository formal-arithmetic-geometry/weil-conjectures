/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.Sites.Torsor
import Sheaf.AlgebraicGeometry.FiniteEtaleClosedSubschemeSection
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Tags 09ZB, 03RV and 09ZA (the geometric step).
(blueprint: lem-weil-pbc-gabber-h1-torsors-trivial).

Proof: Local trivializations identify the underlying sheaf of each torsor with the
finite constant sheaf M. Hence it is finite locally constant. By Tag 03RV it is the
sheaf of sections of a finite etale scheme V over Z; Yoneda transports the M-action.
The morphism V to Z is surjective, since a torsor is locally nonempty. The spectrum
of R is affine, integral and normal, and its function field is FractionRing R, which
is separably closed. Z is affine as a closed subscheme; V is affine as a finite scheme
over Z. Apply Tag 09ZA to obtain a section of V to Z. Under representability this is
a global torsor section t. On each object of the site, the map m to m + t is an
M-equivariant bijection by simple transitivity, and these maps commute with restriction.
They form an equivariant sheaf isomorphism from the trivial torsor to the given one.
This argument also covers the empty scheme and the trivial coefficient group. -/
theorem torsors_trivial_of_finite_etale_sections
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsSepClosed (FractionRing R)] (Z : Scheme.{u})
    (i : Z ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion i]
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] :
    ∀ T : CategoryTheory.Sheaf.Torsor
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)), T ≈ CategoryTheory.Sheaf.Torsor.trivial _ := by
  sorry

end AlgebraicGeometry.Etale
