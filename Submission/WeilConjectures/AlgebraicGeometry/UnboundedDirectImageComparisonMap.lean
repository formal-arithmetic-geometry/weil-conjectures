/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.LeftExactFunctor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Submission.WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageKanRepresentative
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionsFpqcDescent
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonComposition
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonIdentity
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSetTerminalRestriction
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Submission.WeilConjectures.AlgebraicGeometry.SiteRestrictionInjectives
public import Submission.WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
public import Submission.WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import Submission.WeilConjectures.CategoryTheory.ConstantLeftModuleTransport
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
public import Submission.WeilConjectures.CategoryTheory.RightDerivedExactComposite
public import Submission.WeilConjectures.CategoryTheory.RightDerivedPlusCube
public import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Submission.WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
public import Submission.WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
public import Submission.WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import Submission.WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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
(auxiliary; not a blueprint node). -/
noncomputable def unboundedDirectImagePullbackIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g) ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (Etale.upperStar (ModuleCat.{u + 1} A) g)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)).symm

/-- The specified unbounded comparison: transpose the pullback-square identification
followed by the etale derived counit under the pro-etale derived adjunction.
All direct images are total right derived functors on K-injective resolutions.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md, displayed mate
(auxiliary; not a blueprint node). -/
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
