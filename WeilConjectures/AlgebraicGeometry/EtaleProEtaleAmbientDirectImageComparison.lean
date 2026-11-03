/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Ambient étale/pro-étale direct-image comparison

This module states the definition node
`def-sf-etale-proetale-ambient-direct-image-comparison`.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-finite-dualizing.md`, final proof paragraph; the exact inverse-image square is
specified by Stacks Tag 09A6 and the general mate convention by Stacks Tag 07A7.

The declarations below use only the current ordinary module-sheaf derived categories and
site-comparison interfaces. They are given fresh names so this standalone statement module
does not duplicate declarations from the withdrawn scalar-mate provider.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/--
The canonical inverse-image square for the definition node
`def-sf-etale-proetale-ambient-direct-image-comparison`.
Source: the final proof paragraph of `lem-coef-finite-dualizing.md`, with the exact square
from Stacks Tag 09A6. This is the composition of the exact derived pullback identifications,
the site-comparison square, and the canonical localization-composition isomorphisms.
-/
noncomputable def ambientEtaleProEtaleDirectImageComparisonPullbackIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        L(upperStar (ModuleCat.{u + 1} A) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _

/--
The ambient direct-image comparison for the definition node
`def-sf-etale-proetale-ambient-direct-image-comparison`.
Source: the final proof paragraph of `lem-coef-finite-dualizing.md`, using the geometric
adjunction mate convention of Stacks Tag 07A7.
(blueprint: def-sf-etale-proetale-ambient-direct-image-comparison) It is the counit mate of
the preceding inverse-image square and has no invertibility or finiteness hypothesis.
-/
noncomputable def ambientEtaleProEtaleDirectImageComparison
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R(Etale.lowerStar (ModuleCat.{u + 1} A) f) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        R(lowerStar (ModuleCat.{u + 1} A) f) :=
  (mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _
      (ambientEtaleProEtaleDirectImageComparisonPullbackIso A f).hom)).natTrans

end AlgebraicGeometry.ProEtale
