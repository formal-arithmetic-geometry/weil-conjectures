/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # The canonical unbounded direct-image mate

The constructions are reexported by `UnboundedDirectImageComparison`.
Source: blueprint `sk-prop-pe-unbounded-classical-direct-image.md`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Apply the exact inverse images termwise and localize the specified comparison square.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md; the inverse-image
comparison is sk-thm-pe-direct-image-comparison
(blueprint: lem-sfb-unbounded-direct-image-comparison). -/
noncomputable def unboundedDirectImagePullbackIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g) ≪≫
    Functor.mapDerivedCategoryCompIso
      (Etale.upperStar (ModuleCat.{u + 1} A) g)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)

/-- The specified unbounded comparison: transpose the pullback-square identification
followed by the etale derived counit under the pro-etale derived adjunction.
All direct images are total right derived functors on K-injective resolutions.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md, displayed mate
(blueprint: lem-sfb-unbounded-direct-image-comparison). -/
noncomputable def unboundedDirectImageComparisonMap
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K) :=
  ((ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _)
    ((unboundedDirectImagePullbackIso A g).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.counit.app K))

end AlgebraicGeometry.ProEtale
