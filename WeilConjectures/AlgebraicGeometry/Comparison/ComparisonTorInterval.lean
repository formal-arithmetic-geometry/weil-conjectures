/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport

/-!
# Comparison preserves and detects Tor intervals
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- For a finite coefficient ring, bounded-below etale complexes have Tor amplitude in
`[a,b]` exactly when their canonical comparison pullback to the full small pro-etale site
has the same Tor amplitude, tested against every module sheaf on the respective site.
The pro-etale object is expressed in the recorded intrinsic constant-ring presentation
by the canonical exact coefficient realization, after the recorded termwise pullback.
The coefficient `ULift` is the one used by `proEtaleDerivedCategory`.
Source: Stacks, Tags 099T, 099V, 08FZ, 08G0 and 08G1. -/
theorem comparison_torAmplitudeIn_iff
    (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) (a b : ℤ) (_hab : a ≤ b)
    (K : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} A) T a b K.obj ↔
      Scheme.HasProEtaleTorAmplitude T A
        ((finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.obj
          ((siteComparisonDerivedPullbackPlus T (ULift.{u + 1, u} A)).obj K).obj) a b := by
  let F := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  let e := F.mapDerivedCategoryPlusCompatibility.app K
  have hp := intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A T a b _hab
    (((siteComparisonDerivedPullbackPlus T (ULift.{u + 1, u} A)).obj K).obj)
  have he : ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T a b
        (F.mapDerivedCategory.obj K.obj) ↔
      ProEtale.DerivedCategory.torAmplitudeIn
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T a b
          (((siteComparisonDerivedPullbackPlus T (ULift.{u + 1, u} A)).obj K).obj) := by
    constructor
    · exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm
    · exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e
  exact (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn (Λ := ULift.{u + 1, u} A)
    (K := K.obj)).trans
    ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
      (Λ := ULift.{u + 1, u} A) a b K.obj).symm.trans (he.trans hp.symm))

end AlgebraicGeometry.ProEtale
