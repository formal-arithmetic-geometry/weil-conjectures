/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import WeilConjectures.AlgebraicGeometry.PurityRegularSection
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernClasses
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
public import WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.SmoothFibreRegularLocal
public import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
public import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
public import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
public import Mathlib.RingTheory.Smooth.Flat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Regular
public import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.Modules.LocalSectionOfEpi
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientGeometry
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleQuotientEpi
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleSymmetricAlgebraIso
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjSectionCompatibility
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.SmoothPurity.ProjectiveBundleFormula
import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.KummerAdditivity
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalBounds
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Logic.Relation
import Mathlib.LinearAlgebra.Span.Defs
import WeilConjectures.SmoothPurity.LocalGeneratingTuples
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Span.Basic
import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.SixFunctors.ProEtale.RingSheaf.UpperStarSquare
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
import WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.RightDerivedInjectiveSequence
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation
import WeilConjectures.CategoryTheory.Sites.SectionsWithSupport
import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.RightDerivedBaseChangeZeroUnit
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.CategoryTheory.GrothendieckEdgeCocycle
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarStandardCohomology
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckComposablePair
import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import WeilConjectures.CategoryTheory.BoundedBelowSecondFiltration
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCover
import WeilConjectures.CategoryTheory.FilteredQuotientPageMaps
import WeilConjectures.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.CategoryTheory.FilteredComplexBoundariesLECycles
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject
import Mathlib.Order.WithBotTop
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Algebra.Homology.UpperTruncationStepQuotient
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.CategoryTheory.CartanEilenbergTotalResolution
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.CategoryTheory.CartanEilenbergMappedTotal
import WeilConjectures.CategoryTheory.Derived.DerivedInjectiveResolutionNaturality
import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.CategoryTheory.CartanEilenbergAugmentationQuasiIso
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Mathlib.Algebra.Homology.HomologicalBicomplex
import WeilConjectures.Algebra.Homology.UpperTruncationStepSES
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.CategoryTheory.GrothendieckResolutionUnitComparison
import WeilConjectures.CategoryTheory.SpectralObjectBottomFiltration
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.ProperBaseChange.AlgebraicInverseImageOfTransport
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.AlgebraicGeometry.Purity.PurityComparisonUnitInjectiveModel
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonBoundary
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SmoothPurity.Sf.SfCommonStageWeilCohomology
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernFlagFormula
import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Module.ModuleCohomologyConventions
public import WeilConjectures.AlgebraicGeometry.SupportedBottomGluing
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison

/-!
# Localized top Chern classes of regular sections

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
thm-pur-localized-top-chern, properties (L1)--(L4)
(blueprint: thm-pur-localized-top-chern).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c d v v₂ w w₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The degree reindexing in the canonical tensor-shift comparison.
Source: blueprint localized-top-Chern, Tate degrees (blueprint: thm-pur-localized-top-chern).
Proof: expand the successor cast and distribute multiplication by two. -/
theorem localizedChernDegree_succ (r : ℕ) :
    2 * (r : ℤ) + 2 = 2 * ((r + 1 : ℕ) : ℤ) := by
  omega

/-- Assemble the ordered tensor-shift comparison in an abstract abelian category.
Keeping the category abstract prevents repeated normalization of the concrete
sheaf tensor and localization instances in the kernel.
Source: blueprint localized-top-Chern (L4), tensor and shift comparisons
(blueprint: thm-pur-localized-top-chern). -/
def localizedChernTensorPowerMap {C : Type c} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    [∀ K : DerivedCategory C, ((curriedTensor (DerivedCategory C)).obj K).CommShift ℤ]
    [∀ K : DerivedCategory C, ((curriedTensor (DerivedCategory C)).flip.obj K).CommShift ℤ]
    (L : ℤ → C) (B : ℕ → DerivedCategory C)
    (z : B 0 ⟶ (DerivedCategory.singleFunctor C 0).obj (L 0))
    (step : ∀ r : ℕ, B (r + 1) ⟶
      B r ⊗ ((DerivedCategory.singleFunctor C 0).obj (L 1))⟦(2 : ℤ)⟧)
    (mul : ∀ r : ℕ, L r ⊗ L 1 ⟶ L ((r + 1 : ℕ) : ℤ)) :
    (r : ℕ) → B r ⟶ ((DerivedCategory.singleFunctor C 0).obj (L r))⟦2 * (r : ℤ)⟧
  | 0 => z ≫ (shiftFunctorZero _ ℤ).inv.app _
  | r + 1 =>
      step r ≫
      (localizedChernTensorPowerMap L B z step mul r ▷
        ((DerivedCategory.singleFunctor C 0).obj (L 1))⟦(2 : ℤ)⟧) ≫
      (ProEtale.cupTensorShiftIso
        ((DerivedCategory.singleFunctor C 0).obj (L r))
        ((DerivedCategory.singleFunctor C 0).obj (L 1)) (2 * (r : ℤ)) 2).hom ≫
      (ProEtale.cupSingleTensorMap (L r) (L 1) ≫
        (DerivedCategory.singleFunctor C 0).map (mul r))⟦2 * (r : ℤ) + 2⟧' ≫
      eqToHom (congrArg (fun n : ℤ ↦
        ((DerivedCategory.singleFunctor C 0).obj (L ((r + 1 : ℕ) : ℤ)))⟦n⟧)
        (localizedChernDegree_succ r))

/-- Characterize the ordered comparison using the actual zero, successor and
multiplication maps, allowing only transport between equal Hom presentations.
The heterogeneous equations fix all three inputs and the resulting comparison.
Source: blueprint localized-top-Chern, the canonical tensor comparison in (L4)
(blueprint: thm-pur-localized-top-chern). -/
def localizedChernTensorPowerCharacterization
    {C : Type c} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    [∀ K : DerivedCategory C, ((curriedTensor (DerivedCategory C)).obj K).CommShift ℤ]
    [∀ K : DerivedCategory C, ((curriedTensor (DerivedCategory C)).flip.obj K).CommShift ℤ]
    {L₀ : Type c} (line : L₀) {B₀ : Type (max c v)} (powers : B₀)
    {Z : Type w} (zeroMap : Z) {S : Type w} (stepMap : S)
    {M : Type v} (productMap : M) {H : Type w} (γ : H) (r : ℕ) : Prop :=
  ∃ (L : ℤ → C) (B : ℕ → DerivedCategory C)
    (z : B 0 ⟶ (DerivedCategory.singleFunctor C 0).obj (L 0))
    (step : ∀ j : ℕ, B (j + 1) ⟶
      B j ⊗ ((DerivedCategory.singleFunctor C 0).obj (L 1))⟦(2 : ℤ)⟧)
    (mul : ∀ j : ℕ, L j ⊗ L 1 ⟶ L ((j + 1 : ℕ) : ℤ)),
    HEq L line ∧ HEq B powers ∧ HEq z zeroMap ∧ HEq step stepMap ∧
      HEq mul productMap ∧ HEq γ (localizedChernTensorPowerMap L B z step mul r)

/-- The published ordered-power successor is the same tensor object as that used
by the abstract assembler. Naming this equality avoids repeatedly normalizing the
concrete monoidal dictionary in data definitions.
Source: blueprint localized-top-Chern (L4), ordered positive Tate powers
(blueprint: thm-pur-localized-top-chern).
Proof: unfold affineLinearBaseCoefficient at the successor, then derivedTensorRight
and derivedTensor. Both sides are the curried tensor of the preceding power and
ordinaryFiniteLine[2]. The signed Tate sheaf at 1 is finiteEtaleTateLine. -/
theorem localizedChernTwistSucc_eq (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (T : Scheme.{u}) (r : ℕ) :
    Etale.affineLinearBaseCoefficient A m hA T (r + 1) =
      Etale.affineLinearBaseCoefficient A m hA T r ⊗
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A m T hA 1))⟦(2 : ℤ)⟧ := by
  sorry

/-- The degree-zero comparison in the ordered Tate presentation.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistZero (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (T : Scheme.{u}) :
    Etale.affineLinearBaseCoefficient A m hA T 0 ⟶
      (DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A m T hA 0) :=
  𝟙 _

/-- The canonical successor comparison, as transport through the named equality.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistStep (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (T : Scheme.{u}) (r : ℕ) :
    Etale.affineLinearBaseCoefficient A m hA T (r + 1) ⟶
      Etale.affineLinearBaseCoefficient A m hA T r ⊗
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A m T hA 1))⟦(2 : ℤ)⟧ :=
  eqToHom (localizedChernTwistSucc_eq A m hA T r)

/-- The existing normalized product with its integer index reexpressed as a successor.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistProduct (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (r : ℕ) :
    Scheme.finiteEtaleTateSheaf A m T hA r ⊗ Scheme.finiteEtaleTateSheaf A m T hA 1 ⟶
      Scheme.finiteEtaleTateSheaf A m T hA (r + 1 : ℕ) :=
  (functorialCupTwistProductGeneral A m hm hA T hT r 1).hom ≫
    eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m T hA)
      (Int.natCast_succ r).symm)

/-- Canonical comparison from ordered shifted root powers to the single signed
Tate sheaf shifted by twice its weight. The abstract assembler uses the actual
localization tensor map, right-shift-first comparison, and normalized product.
Source: blueprint localized-top-Chern (L4) and coefficient-twist conventions
(blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistMapEtaleRawCharacterization (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (r : ℕ)
    (γ : Etale.affineLinearBaseCoefficient A m hA T r ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m T hA r))⟦2 * (r : ℤ)⟧) : Prop :=
  localizedChernTensorPowerCharacterization
    (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Scheme.finiteEtaleTateSheaf A m T hA)
    (Etale.affineLinearBaseCoefficient A m hA T)
    (localizedChernTwistZero A m hA T) (localizedChernTwistStep A m hA T)
    (localizedChernTwistProduct A m hm hA T hT) γ r

/-- The explicit canonical map has exactly one realization in these coordinates.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern).
Proof: unfold the named characterization. The two Hom types agree by unfolding
singleFunctor and the existing Tate/constant definitions. Transport the displayed
map through that equality; heterogeneous equality gives uniqueness. -/
theorem localizedChernTwistMapEtaleRaw_realization (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (r : ℕ) :
    ∃! γ : Etale.affineLinearBaseCoefficient A m hA T r ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m T hA r))⟦2 * (r : ℤ)⟧,
      localizedChernTwistMapEtaleRawCharacterization A m hm hA T hT r γ := by
  sorry

/-- The uniquely specified explicit comparison in the published coordinates.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistMapEtaleRaw (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (r : ℕ) :
    Etale.affineLinearBaseCoefficient A m hA T r ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m T hA r))⟦2 * (r : ℤ)⟧ :=
  (localizedChernTwistMapEtaleRaw_realization A m hm hA T hT r).choose

/-- The same canonical tensor-shift comparison at the chapter's fixed coefficients.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistMapEtale (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) (r : ℕ) : P.diagonalTwistEtale T r ⟶
      ((P.functorialCupSingle false T).obj (P.functorialCupTwist false T r))⟦2 * (r : ℤ)⟧ :=
  localizedChernTwistMapEtaleRaw P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates T (P.diagonalExponent_isUnit a) r

/-- Transport a class through an exact functor and a specified target comparison,
using only its canonical single-object and shift isomorphisms.
Source: blueprint localized-top-Chern (L4), etale-to-pro-etale comparison
(blueprint: thm-pur-localized-top-chern). -/
def localizedChernClassTransport {C : Type c} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {D : Type d} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₂} D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (U L : C) (K : DerivedCategory C) (n : ℤ)
    (α : F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj U) ⟶
      F.mapDerivedCategory.obj K)
    (τ : K ⟶ ((DerivedCategory.singleFunctor C 0).obj L)⟦n⟧) :
    (DerivedCategory.singleFunctor D 0).obj (F.obj U) ⟶
      ((DerivedCategory.singleFunctor D 0).obj (F.obj L))⟦n⟧ :=
  (F.mapDerivedCategorySingleFunctor 0).inv.app U ≫ α ≫
    F.mapDerivedCategory.map τ ≫
    (F.mapDerivedCategory.commShiftIso n).hom.app
      ((DerivedCategory.singleFunctor C 0).obj L) ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app L)⟦n⟧'

/-- The ordinary Chern class in the identical supported-cup target coordinates.
The source single-comparison and target shift-comparison are the canonical exact
comparison inverse image, not a chosen cohomology equivalence.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernOrdinaryCharacterization (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (γ : P.FunctorialCupOrdinaryH true T (2 * (r : ℤ)) r) : Prop :=
  @HEq _ γ _ (localizedChernClassTransport (P.functorialCupComparisonFunctor T)
    (P.constantEtale T) (P.functorialCupTwist false T r) (P.diagonalTwistEtale T r)
    (2 * (r : ℤ)) (P.ordinaryFiniteChernClass a F r r)
    (P.localizedChernTwistMapEtale T a r))

/-- The explicit canonical map has exactly one realization in these coordinates.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern).
Proof: unfold the named characterization. The two Hom types agree by unfolding
singleFunctor and the existing Tate/constant definitions. Transport the displayed
map through that equality; heterogeneous equality gives uniqueness. -/
theorem localizedChernOrdinary_realization (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r] :
    ∃! γ : P.FunctorialCupOrdinaryH true T (2 * (r : ℤ)) r,
      localizedChernOrdinaryCharacterization P a F r γ := by
  sorry

/-- The uniquely specified explicit comparison in the published coordinates.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernOrdinary (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r] :
    P.FunctorialCupOrdinaryH true T (2 * (r : ℤ)) r :=
  (localizedChernOrdinary_realization P a F r).choose

/-- A family of supported morphisms for the regular sections in the statement.
Source: blueprint localized-top-Chern, displayed arrow
(blueprint: thm-pur-localized-top-chern). -/
abbrev LocalizedTopChernClasses (P : PurityFiniteSetting.{u}) :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] (s : F.sections),
    IsRegularSection P T a F r s →
      P.FunctorialCupH true (regularSectionZeroProjection P T a F r s) (2 * (r : ℤ)) r

/-- The zero scheme is closed, and forgetting support gives the existing ordinary
top Chern class. Source: blueprint (L4) (blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernForgetSupport (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] (s : F.sections) (hs : IsRegularSection P T a F r s),
  ∃ hc : IsClosedImmersion (regularSectionZeroProjection P T a F r s),
    @functorialCupForget P true _ _ (regularSectionZeroProjection P T a F r s)
      hc (2 * (r : ℤ)) r (c a F r s hs) = P.localizedChernOrdinary a F r

/-- In rank one the class is the normalized relative-torsor Cartier class of s.
Source: blueprint (L1) (blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernLine (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank 1] (s : F.sections) (hs : IsRegularSection P T a F 1 s),
  ∃ (hc : IsClosedImmersion (regularSectionZeroProjection P T a F 1 s))
    (hI : (regularSectionZeroProjection P T a F 1 s).ker.IsInvertible)
    (D : P.DivisorEtaleClasses T),
    P.DivisorEtaleNormalized T a D ∧
      c a F 1 s hs = @divisorProEtale P _ _
        (regularSectionZeroProjection P T a F 1 s) hc
        (@DivisorEtaleClasses.homClassOf P T D _
          (regularSectionZeroProjection P T a F 1 s) hc hI)

/-- Arbitrary base change when the pulled-back section remains regular. The
canonical Cartesian square is a conclusion, not an additional assumption.
Source: blueprint (L2) (blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernBaseChange (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T T' : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (g : T' ⟶ T)
    [IsSeparated (g ≫ a)] [LocallyOfFiniteType (g ≫ a)] [QuasiCompact (g ≫ a)]
    (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) (hs : IsRegularSection P T a F r s)
    (F' : T'.Modules) [F'.IsFiniteLocallyFreeOfRank r]
    (e : (Scheme.Modules.tensorPullback g).obj F ≅ F') (s' : F'.sections)
    (_he : ∀ U : T.Opens,
      e.hom.val.app (op (g ⁻¹ᵁ U))
          (Scheme.Modules.tensorPullbackSection g F U (s.val (op U))) =
        s'.val (op (g ⁻¹ᵁ U)))
    (hs' : IsRegularSection P T' (g ≫ a) F' r s'),
  ∃ (hc : IsClosedImmersion (regularSectionZeroProjection P T a F r s))
    (hc' : IsClosedImmersion (regularSectionZeroProjection P T' (g ≫ a) F' r s'))
    (gZ : regularSectionZeroScheme P T' (g ≫ a) F' r s' ⟶
      regularSectionZeroScheme P T a F r s)
    (sq : ChosenCartesianSquare gZ (regularSectionZeroProjection P T' (g ≫ a) F' r s')
      (regularSectionZeroProjection P T a F r s) g),
    @functorialCupPullback P true _ _ _ _
      (regularSectionZeroProjection P T a F r s)
      (regularSectionZeroProjection P T' (g ≫ a) F' r s') hc hc' g gZ sq a
      (2 * (r : ℤ)) r (c a F r s hs) = c (g ≫ a) F' r s' hs'

/-- The internal cup product on the scheme-theoretic intersection, identified
with the zero scheme of the actual direct sum section. Source: blueprint (L3)
(blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernDirectSum (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) (hs : IsRegularSection P T a F r s)
    (ht : IsRegularSection P T a G e t) (_htr : IsTransverseDirectSum P T a F G r e s t),
  ∃ (hFG : (F ⨯ G).IsFiniteLocallyFreeOfRank (r + e))
    (hst : @IsRegularSection P T a _ _ _ (F ⨯ G) (r + e) hFG
      (regularSectionSum F G s t))
    (hc : IsClosedImmersion (regularSectionZeroProjection P T a F r s))
    (hd : IsClosedImmersion (regularSectionZeroProjection P T a G e t))
    (hi : IsClosedImmersion (regularSectionIntersectionProjection P T a F G r e s t))
    (hj : IsClosedImmersion (regularSectionSumZeroProjection P T a F G r e s t))
    (hproj : (regularSectionSumZeroComparison P T a F G r e s t).hom ≫
        regularSectionIntersectionProjection P T a F G r e s t =
      regularSectionSumZeroProjection P T a F G r e s t),
    HEq (@functorialCupChangeSupport P true _ _ _
      (regularSectionIntersectionProjection P T a F G r e s t)
      (regularSectionSumZeroProjection P T a F G r e s t) hi hj
      (regularSectionSumZeroComparison P T a F G r e s t).hom hproj
      (2 * ((r + e : ℕ) : ℤ)) (r + e : ℕ)
      (@c T a _ _ _ (F ⨯ G) (r + e) hFG (regularSectionSum F G s t) hst))
    (@functorialCup P true _ _ _ a
      (regularSectionZeroProjection P T a F r s)
      (regularSectionZeroProjection P T a G e t) hc hd
      (2 * (r : ℤ)) (2 * (e : ℤ)) r e (c a F r s hs) (c a G e t ht))

/-- Exactly the four properties of the localized class, factored as named predicates
so the kernel checks each geometric law once.
Source: blueprint localized-top-Chern, (L1)--(L4)
(blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernLaws (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  P.LocalizedTopChernForgetSupport c ∧ P.LocalizedTopChernLine c ∧
    P.LocalizedTopChernBaseChange c ∧ P.LocalizedTopChernDirectSum c

/-- The line clause of the four localized Chern laws.
Source: blueprint localized-top-Chern, (L1)--(L4)
(blueprint: thm-pur-localized-top-chern).
Proof: project the corresponding conjunct of LocalizedTopChernLaws. -/
theorem LocalizedTopChernLaws.line (P : PurityFiniteSetting.{u})
    {c : P.LocalizedTopChernClasses} (h : P.LocalizedTopChernLaws c) :
    P.LocalizedTopChernLine c := by
  exact h.2.1

end WeilConjectures.PurityFiniteSetting
