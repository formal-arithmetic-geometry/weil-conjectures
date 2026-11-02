/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.ScalarPullbackMateInvertible
public import WeilConjectures.AlgebraicGeometry.EtaleChartComparison.EtaleChartComparisonIsos
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleAmbientDirectImageComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # Normalized scalar/pullback comparisons and bounded-below ambient mate

Source: lem-fix-compact-support-coefficient-change, pullback compatibility and final
site transport; det-prop-scalar-six-direct-image, Finite rings; Stacks 06YY, 09A6.
(blueprint: lem-sfb-scalar-site-comparison-normalized-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.OrdinaryScalarSite

/-- The published scalar extension left adjoint to actual exact derived restriction.
Source: Stacks 06YY; def-sp-coefficient-scalar-representatives
(blueprint: lem-sfb-scalar-site-comparison-normalized-data). -/
abbrev scalar {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) := CoefficientScalarRepresentatives.extension J a

/-- The forward pro-etale comparison is the inverse of the published scalar mate,
transported through the specified exact geometric comparisons.
Source: Stacks 06YY, 07A4
(blueprint: lem-sfb-scalar-site-comparison-normalized-data). -/
def proEtaleIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalar (Scheme.ProEt.topology Y) a ⋙
        (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        scalar (Scheme.ProEt.topology X) a :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm ≪≫
    (@asIso _ _ _ _
      (((mateEquiv
        (CoefficientScalarRepresentatives.adjunction (Scheme.ProEt.topology Y) a)
        (CoefficientScalarRepresentatives.adjunction (Scheme.ProEt.topology X) a)).symm
          (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso a f).hom)).natTrans)
      (CoefficientScalarRepresentatives.proEtaleScalarPullbackMate_isIso a f)).symm ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) _

end AlgebraicGeometry.ProEtale.OrdinaryScalarSite
