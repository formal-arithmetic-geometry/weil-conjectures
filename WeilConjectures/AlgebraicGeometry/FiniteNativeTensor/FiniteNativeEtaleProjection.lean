/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
import WeilConjectures.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # The native etale projection in a fixed import context

The definition retains every implicit structure of the upstream projection.
(blueprint: lem-pur-finite-native-etale-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.ProEtale.FiniteNativeTensor

/-- The literal upstream compactification projection, with its type inferred from that map.
Source: `Etale.projectionMapOfCompactification`
(blueprint: lem-pur-finite-native-etale-projection). -/
def canonicalEtaleProjection (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y) :=
  ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K

/-- Finite coefficients give invertibility of the actual projection.
Source: `Etale.sfEtaleAmbientAdjointProjection`, by specialization
(blueprint: lem-pur-finite-native-etale-projection). -/
theorem canonicalEtaleProjection_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y) :
    IsIso (canonicalEtaleProjection A c M K) :=
  (Etale.sfEtaleAmbientAdjointProjection A c).2 M K

/-- Naturality in the compactly supported input, from bifunctor naturality.
Source: `Etale.projectionMapOfCompactification`
(blueprint: lem-pur-finite-native-etale-projection). -/
theorem canonicalEtaleProjection_natural_left (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {M N : Etale.DerivedCategoryModule A X} (r : M ⟶ N)
    (K : Etale.DerivedCategoryModule A Y) :
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map r ▷ K ≫
        canonicalEtaleProjection A c N K =
      canonicalEtaleProjection A c M K ≫
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (r ▷ (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K) :=
  NatTrans.congr_app ((Etale.projectionMapOfCompactification
    (ModuleCat.{u + 1} A) c).naturality r) K

end AlgebraicGeometry.ProEtale.FiniteNativeTensor
