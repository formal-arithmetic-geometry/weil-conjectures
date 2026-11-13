/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.GabberConstantH1Vanishing
import WeilConjectures.AlgebraicGeometry.GabberPrincipalOpenClosedPresentation
import WeilConjectures.AlgebraicGeometry.ConstantEtaleCohomologyIsoComparison
import WeilConjectures.ConstructibleSheaf.Defs

/-! # Degree-one vanishing on principal opens of a quotient

## References

* [Stacks Project, Tag 09ZC](https://stacks.math.columbia.edu/tag/09ZC)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- First cohomology of the restriction of a finite constant sheaf to each principal
open of `Spec (R/I)` is zero (Stacks, Tag 09ZC). -/
theorem gabber_quotient_principal_h1
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hsep : IsSepClosed (FractionRing R)) (I : Ideal R)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] (h : R ⧸ I) :
    Subsingleton (Sheaf.H.{u + 1}
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of (R ⧸ I)))
        (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj
          ((constantSheaf (Spec (CommRingCat.of (R ⧸ I))).smallEtaleTopology
            AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))) 1) := by
  obtain ⟨S, hdom, hnormal, hS, i, hi⟩ :=
    gabber_principal_open_closed_presentation R hsep I h
  let := hdom
  let := hnormal
  let := hS
  let := hi
  let U := Scheme.Opens.toScheme (X := Spec (CommRingCat.of (R ⧸ I)))
    (PrimeSpectrum.basicOpen h)
  have hz := isZero_constant_cohomology_one_of_isIntegrallyClosed S U i M
  have hc := (isZero_constant_cohomology_iff_subsingleton_H_of_iso
    U U (Iso.refl U) M 1).mp hz
  let e := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
    (Scheme.Opens.ι (X := Spec (CommRingCat.of (R ⧸ I)))
      (PrimeSpectrum.basicOpen h))).app (AddCommGrpCat.of M)
  let eH := ((Sheaf.functorH.{u + 1} U.smallEtaleTopology 1).mapIso e).addCommGroupIsoToAddEquiv
  exact @Equiv.subsingleton _ _ eH.toEquiv hc

end AlgebraicGeometry.Etale
