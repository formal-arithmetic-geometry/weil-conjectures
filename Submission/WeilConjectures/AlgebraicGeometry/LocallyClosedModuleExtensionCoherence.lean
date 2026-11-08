/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Submission.WeilConjectures.AlgebraicGeometry.LocallyClosedModuleExtensionData
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import Submission.WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import Submission.WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import Submission.WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import Submission.WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import Submission.WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleConstruction
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Submission.WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import Submission.WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import Submission.WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import Submission.WeilConjectures.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Submission.WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import Submission.WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import Submission.WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
import Submission.WeilConjectures.AlgebraicGeometry.SemilinearGeometryDerived
import Submission.WeilConjectures.AlgebraicGeometry.SemilinearModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
import Submission.WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import Submission.WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Submission.WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperations
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import Submission.WeilConjectures.CategoryTheory.Adjunction.MateCube
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Submission.WeilConjectures.CategoryTheory.DerivedExactMate
import Submission.WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import Submission.WeilConjectures.CategoryTheory.ExactDerivedAdjunction
import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import Submission.WeilConjectures.CategoryTheory.RightDerivedPlusCube
import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
import Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import Submission.WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
import Submission.WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import Submission.WeilConjectures.RingTheory.FactorsThroughLocalization
import Submission.WeilConjectures.RingTheory.FilteredColimitOfFactorization
import Submission.WeilConjectures.SecSmoothPurity.CochainCoefficientArrows
import Submission.WeilConjectures.SecSmoothPurity.CochainInverseComparison
import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Submission.WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import Submission.WeilConjectures.SixFunctors.Etale.Derived.HeartGluing
import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import Submission.WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareComponent
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! Normalized locally closed module extension: assembly from the fixed model. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Witnesses for the exact module extensions in the assertion. The open adjunction and
closed counit normalize restriction. The coefficients of every arrow are inverse images.
Source: Stacks, Tags 09AA, 09BM, 09BN, 03DI and 03DJ
(auxiliary; not a blueprint node). -/
structure LocallyClosedExtensionData where
  extension : ∀ {S X : LocallyClosedCoefficients.{u}}, LocallyClosedCoefficientImmersion S X →
    proEtaleRingModules S.scheme S.ring ⥤ proEtaleRingModules X.scheme X.ring
  additive : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (extension a).Additive
  finiteLimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteLimits (extension a)
  finiteColimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteColimits (extension a)
  restriction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), extension a ⋙ a.pull ≅ 𝟭 _
  openAdjunction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsOpenImmersion a.hom),
    extension a ⊣ a.pull
  openNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsOpenImmersion a.hom),
    LocallyClosedOpenNormalization (extension a) a.pull (restriction a) (openAdjunction a ha)
  closedComparison : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsClosedImmersion a.hom),
    extension a ≅ a.push
  closedNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsClosedImmersion a.hom),
    LocallyClosedClosedNormalization (extension a) a.push a.pull (restriction a)
      (proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).counit
      (closedComparison a ha)
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    extension b ⋙ extension a ≅ extension (a.comp b)
  identity : ∀ X : LocallyClosedCoefficients.{u},
    extension (.identity X) ≅ 𝟭 (proEtaleRingModules X.scheme X.ring)

attribute [instance] LocallyClosedExtensionData.additive LocallyClosedExtensionData.finiteLimits
  LocallyClosedExtensionData.finiteColimits

namespace LocallyClosedExtensionData

/-- The actual termwise extension on the ordinary unbounded derived categories.
Source: Stacks, Tags 015F and 05RU
(auxiliary; not a blueprint node). -/
abbrev derived (E : LocallyClosedExtensionData.{u}) {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) := (E.extension a).mapDerivedCategory

/-- The same comparisons on unbounded derived categories, required to be the
localizations of the module comparisons on every cochain complex, not arbitrary isos.
Source: Stacks, Tags 05RU and 015F; exact-functor localization
(auxiliary; not a blueprint node). -/
structure DerivedCoherence (E : LocallyClosedExtensionData.{u}) where
  restriction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), E.derived a ⋙ a.pull.mapDerivedCategory ≅ 𝟭 _
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    E.derived b ⋙ E.derived a ≅ E.derived (a.comp b)
  identity : ∀ X : LocallyClosedCoefficients.{u}, E.derived (.identity X) ≅ 𝟭 _
  restrictionTermwise : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X)
    (K : CochainComplex (proEtaleRingModules S.scheme S.ring) ℤ),
    (restriction a).hom.app (DerivedCategory.Q.obj K) =
      a.pull.mapDerivedCategory.map ((E.extension a).mapDerivedCategoryFactors.hom.app K) ≫
        a.pull.mapDerivedCategoryFactors.hom.app
          (((E.extension a).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (E.restriction a) (.up ℤ)).hom.app K)
  gammaTermwise : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (K : CochainComplex (proEtaleRingModules T.scheme T.ring) ℤ),
    (gamma a b).hom.app (DerivedCategory.Q.obj K) ≫
        (E.extension (a.comp b)).mapDerivedCategoryFactors.hom.app K =
      (E.derived a).map ((E.extension b).mapDerivedCategoryFactors.hom.app K) ≫
        (E.extension a).mapDerivedCategoryFactors.hom.app
          (((E.extension b).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (E.gamma a b) (.up ℤ)).hom.app K)
  identityTermwise : ∀ (X : LocallyClosedCoefficients.{u})
    (K : CochainComplex (proEtaleRingModules X.scheme X.ring) ℤ),
    (identity X).hom.app (DerivedCategory.Q.obj K) =
      (E.extension (.identity X)).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (E.identity X) (.up ℤ)).hom.app K)
  full : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (E.derived a).Full
  faithful : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), (E.derived a).Faithful
  homBijection : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X)
    (M N : DerivedCategory (proEtaleRingModules S.scheme S.ring)),
    Function.Bijective (fun f : (E.derived a).obj M ⟶ (E.derived a).obj N ↦
      (restriction a).inv.app M ≫ a.pull.mapDerivedCategory.map f ≫ (restriction a).hom.app N)
  innerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : a.comp (.identity S) = a,
      gamma a (.identity S) ≪≫ eqToIso (congrArg E.derived h) =
        Functor.isoWhiskerRight (identity S) (E.derived a) ≪≫ Functor.leftUnitor (E.derived a)
  outerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      gamma (.identity X) a ≪≫ eqToIso (congrArg E.derived h) =
        Functor.isoWhiskerLeft (E.derived a) (identity X) ≪≫ Functor.rightUnitor (E.derived a)
  associative : ∀ {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T),
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (gamma b d) (E.derived a) ≪≫ gamma a (b.comp d) =
        Functor.associator (E.derived d) (E.derived b) (E.derived a) ≪≫
          Functor.isoWhiskerLeft (E.derived d) (gamma a b) ≪≫ gamma (a.comp b) d ≪≫
            eqToIso (congrArg E.derived h)

end LocallyClosedExtensionData

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage

private structure OpenNormalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) where
  adj : F ⊣ L
  normalized : LocallyClosedOpenNormalization F L r adj

private structure ClosedNormalization
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C) where
  iso : F ≅ P
  normalized : LocallyClosedClosedNormalization F P L r d iso

end AlgebraicGeometry.Scheme
