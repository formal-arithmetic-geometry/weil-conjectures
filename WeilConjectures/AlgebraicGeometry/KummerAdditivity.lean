/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.CategoryTheory.DeltaFunctor
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Additivity and pullback of the finite Kummer first Chern class

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/lem-pur-kummer-additivity;
Stacks Project, Tags 03PL, 03AJ, 040E, 03FD, 08JA and 099R
(blueprint: lem-pur-kummer-additivity).

The finite-root presentation is the one reexported by `FixedFinitePositiveCoefficientTwist`:
comparison inverse image of mu_(ell^N) tensor A represents the specified finite Tate line.
There is no tensor product of G_m with A, and no ramification-divisibility assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The class H²(phi)(delta(alpha(M))), with alpha the canonical frame-torsor class.
Source: Stacks Tags 03PL, 03AJ and 040E (blueprint: lem-pur-kummer-additivity). -/
def kummerFirstChernAbelian (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (M : T.Pic) :
    Sheaf.H ((RawModuleScalarComparison.forget A T).obj
      (Scheme.finiteEtaleTateLine T m A hA)) 2 :=
  Sheaf.H.map (ordinaryFiniteRootMap A m hA T) 2
    (T.kummerδ₁ m hT (Scheme.Pic.toCohomologicalPicardGroup T M))

/-- The unique derived morphism realizing the actual Kummer boundary class.
Source: Stacks Tags 03PL, 03FD and 08JA (blueprint: lem-pur-kummer-additivity). -/
def kummerFirstChern (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (M : T.Pic) :
    ordinaryFiniteUnit A T ⟶ (ordinaryFiniteLine A m hA T)⟦(2 : ℤ)⟧ :=
  (Equiv.ofBijective (ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T m A hA) 2)
    (ordinaryFiniteClass_bijective_arbitraryBase A T _ 2)).symm
      (kummerFirstChernAbelian A m hA T hT M)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- The finite Kummer Chern class on the small pro-etale site, in the finite-root
presentation of the recorded Tate line. The comparison is applied termwise, exactly
as in siteComparisonDerivedPullbackPlus, on its unbounded ambient category.
Source: Stacks Tag 099R and the finite reduction of def-coefficient-twists-detailed
(blueprint: lem-pur-kummer-additivity). -/
def kummerFirstChern (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (M : T.Pic) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        ((Etale.ordinaryFiniteLine A m hA T)⟦(2 : ℤ)⟧) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
    (Etale.kummerFirstChern A m hA T hT M)

/-- The canonical square comparison g* nu* = nu* g*, by the inverse-image adjunctions
and exact termwise descent. Source: Stacks Tags 03CB and 099R
(blueprint: lem-pur-kummer-additivity). -/
def kummerComparisonPullback (A : Type (u + 1)) [CommRing A]
    {T T' : Scheme.{u}} (f : T' ⟶ T) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ≅
      Etale.ordinaryFinitePullback A f ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T').mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _

/-- Pullback of a compared finite coefficient object, through the canonical square.
Source: Stacks Tags 03CB and 099R (blueprint: lem-pur-kummer-additivity). -/
def kummerCoefficientPullback (A : Type (u + 1)) [CommRing A]
    {T T' : Scheme.{u}} (f : T' ⟶ T)
    (K : Etale.DerivedCategoryModule A T) (K' : Etale.DerivedCategoryModule A T')
    (e : (Etale.ordinaryFinitePullback A f).obj K ≅ K') :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K) ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) T').mapDerivedCategory.obj K' :=
  (kummerComparisonPullback A f).app K ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) T').mapDerivedCategory.mapIso e

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

end WeilConjectures.PurityFiniteSetting
