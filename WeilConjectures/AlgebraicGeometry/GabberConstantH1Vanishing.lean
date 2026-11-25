/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.GabberH1TorsorCohomologyBridge
import WeilConjectures.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial

/-!
# Gabber's vanishing of first constant étale cohomology

## References

* Stacks Project, Étale Cohomology, Lemma 09ZB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a normal domain with separably closed fraction field, first étale cohomology of any
finite constant abelian sheaf on any closed subscheme of its spectrum vanishes.
(Stacks, Lemma 09ZB) -/
theorem isZero_constant_cohomology_one_of_isIntegrallyClosed
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsSepClosed (FractionRing R)] (Z : Scheme.{u})
    (i : Z ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion i]
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] :
    IsZero ((cohomology AddCommGrpCat.{u + 1} Z 1).obj
      ((DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)))) := by
  apply isZero_constant_cohomology_one_of_torsors_trivial R Z i M
  exact torsors_trivial_of_finite_etale_sections R Z i M

end AlgebraicGeometry.Etale
