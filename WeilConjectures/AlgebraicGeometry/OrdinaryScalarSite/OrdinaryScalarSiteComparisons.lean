/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryScalarSite.ScalarSiteComparisonNormalizedData
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate

/-! # Ordinary scalar/site delta and direct-image gamma mates

Source: det-prop-scalar-six-direct-image, Formal properties and Finite rings;
Stacks 03EL, 06YY, 07A7.
(blueprint: def-sfb-ordinary-scalar-site-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.TwoSquare
namespace AlgebraicGeometry.ProEtale.OrdinaryScalarSite

/-- Delta is the published scalar/site inverse mate, equipped with its inverse.
Source: det-prop-scalar-six-direct-image, Finite rings; Stacks 07A4
(blueprint: def-sfb-ordinary-scalar-site-comparisons). -/
abbrev delta {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (T : Scheme.{u}) :=
  CoefficientScalarRepresentatives.comparisonIso T a

/-- The scalar direct-image mate on the etale site. Its transpose is scalar
extension of the counit after the normalized pullback/tensor comparison.
Source: det-prop-scalar-six-direct-image, Formal properties; Stacks 07A7
(blueprint: def-sfb-ordinary-scalar-site-comparisons). -/
def etaleGamma {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (mateEquiv
    (Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (etaleIso a f).hom).natTrans

/-- The scalar direct-image mate on the pro-etale site. This construction does
not invert the mate. Source: det-prop-scalar-six-direct-image; Stacks 07A7
(blueprint: def-sfb-ordinary-scalar-site-comparisons). -/
def proEtaleGamma {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (mateEquiv
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f))
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f))
    (proEtaleIso a f).hom).natTrans

end AlgebraicGeometry.ProEtale.OrdinaryScalarSite
