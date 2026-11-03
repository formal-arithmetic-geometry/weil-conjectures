/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonCoefficientsSupplement
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
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
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.CategoryTheory.Sites.LocalSite
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonLocal
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonClassical
import WeilConjectures.AlgebraicGeometry.CoefficientStratifiedContinuity
import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemOrigin
import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantEtaleSections
import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantCounit
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.Presheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Data.Finite.Prod
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartCounit
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.CoefficientStratifiedEssentialImage
import WeilConjectures.AlgebraicGeometry.CoefficientOriginOpenCover
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.AlgebraicGeometry.CoefficientOriginAffineOpenClosed
import WeilConjectures.AlgebraicGeometry.CoefficientOriginClosedDirectImage
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonModelRealizationSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonContinuity
import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonRepresentableContinuity
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import WeilConjectures.AlgebraicGeometry.AffinePresentationSectionColimit
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitMaps
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitFactorization
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitEquality
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Topology.Spectral.ConstructibleTopology
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.RingTheory.IndEtaleSmallIndex
import WeilConjectures.RingTheory.ProEtale.Etale
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonPresentationSheafification
import WeilConjectures.AlgebraicGeometry.CoefficientClassicalModuleOrigin
import WeilConjectures.AlgebraicGeometry.CoefficientOriginLocalizationKernel
import WeilConjectures.AlgebraicGeometry.CoefficientFixedLocalizationKernelComparison
import WeilConjectures.AlgebraicGeometry.CoefficientFixedClosedUnitEpi
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.AlgebraicGeometry.CoefficientOpenClosedKernel
import WeilConjectures.AlgebraicGeometry.CoefficientOpenExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonInjectiveAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonAffineSections
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonAffineCech
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.AlgebraicGeometry.CoefficientAffineCechPresentation
import WeilConjectures.AlgebraicGeometry.CoefficientAffineCechSystem
import WeilConjectures.AlgebraicGeometry.CechNervePresentationConstruction
import WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
import WeilConjectures.CategoryTheory.Sites.CechComplex
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.CategoryTheory.Pro.Generating
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.CategoryTheory.Sites.CechComplexRelativeLimit
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechExact
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.CategoryTheory.ModuleCechCriterion
import WeilConjectures.CategoryTheory.SiteSesCechH1Surjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.Topology.ConstructibleIsRetrocompact
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonModuleEquivalence
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonModuleCriteria
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor
import WeilConjectures.AlgebraicGeometry.CoefficientClassicalSingle
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedClassicalDescent
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstructibilityTest
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFiniteReflection
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartReflection
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Defs.Filter
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.CoefficientTorFlatModelSupplement
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorPairingIsIso
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.RingedTopoiScalarTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonFaithful
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.FiniteAdmissibleGeneration
public import WeilConjectures.AlgebraicGeometry.FiniteComparisonPresentationSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible

/-!
# Finite coefficient comparison on localizing closures

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ctf-finite-comparison/
sk-prop-ctf-finite-comparison-localizing.md
(blueprint: det-ctf-finite-comparison-localizing).

## Main definitions

* `finiteComparisonRealization`: the specified finite-discrete coefficient transport.
* `finiteComparisonEtaleClosure`, `finiteComparisonProEtaleClosure`: the two closures.
* `finiteComparisonOpenIso`, `finiteComparisonCompactSupportMap`: the canonical arrows.

## Main statements

* `finiteComparisonRealization_exact`: exactness of the specified coefficient transport.
* `finiteComparisonLocalizing`: the equivalence and its compatibility with operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ZeroObject

section LocalizingArgument
universe w v₁ v₂
namespace CategoryTheory

variable {C : Type w} {D : Type w} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

private theorem closureLocalizing (S : ObjectProperty C) :
    IsLocalizingSubcategory (localizingClosure S) := by
  have hiso : (localizingClosure S).IsClosedUnderIsomorphisms := by
    constructor
    intro K L e hK P hP hS
    let := hP.2.1
    exact P.prop_of_iso e (hK P hP hS)
  let := hiso
  have hzero : (localizingClosure S).ContainsZero := by
    refine ⟨0, isZero_zero _, ?_⟩
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.prop_zero
  let := hzero
  have hshift : (localizingClosure S).IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro K hK
    rw [ObjectProperty.prop_shift_iff]
    intro P hP hS
    let := hP.1
    exact P.le_shift n K (hK P hP hS)
  let := hshift
  have htri : (localizingClosure S).IsTriangulated := by
    refine { ext₂' := ?_ }
    intro T hT h₁ h₃
    apply ObjectProperty.le_isoClosure
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hS) (h₃ P hP hS)
  refine ⟨htri, hiso, ?_⟩
  intro I F hF hK
  change ∀ P, IsLocalizingSubcategory P → (∀ K, S K → P K) → _
  intro P hP hS
  exact hP.2.2 F hF (fun i ↦ hK i P hP hS)

private theorem inverseImageLocalizing (P : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F]
    (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.inverseImage F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I G hG hPG
  let := hG
  let : HasColimit (G ⋙ F) := ⟨_, isColimitOfPreserves F (colimit.isColimit G)⟩
  exact P.prop_of_iso (preservesColimitIso F G).symm
    (hP.2.2 (G ⋙ F) inferInstance hPG)

private theorem imageLocalizing (P : ObjectProperty C) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [Coreflective F] (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.map F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I H hH hPH
  let := hH
  have hHF (j : Discrete I) : F.essImage (H.obj j) := by
    obtain ⟨K, _, e⟩ := hPH j.as
    exact ⟨K, e⟩
  let G := Functor.essImage.liftFunctor H F hHF
  let e := Functor.essImage.liftFunctorCompIso H F hHF
  let : HasColimit (G ⋙ F) := hasColimit_of_iso e
  let : HasColimit G := hasColimit_of_coreflective G F
  have hPG (i : I) : P (G.obj (Discrete.mk i)) := by
    obtain ⟨K, hK, ⟨iK⟩⟩ := hPH i
    exact P.prop_of_iso (F.preimageIso (iK ≪≫ (e.app (Discrete.mk i)).symm)) hK
  refine ⟨colimit G, hP.2.2 G inferInstance hPG, ⟨?_⟩⟩
  exact (preservesColimitIso F G) ≪≫ HasColimit.isoOfNatIso e

private theorem closureEquivalence (S : ObjectProperty C) (T : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [Coreflective F]
    (hS : ∀ K, S K → localizingClosure T (F.obj K))
    (hT : ∀ K, T K → (localizingClosure S).map F K) :
    ∃ hpres : ∀ K, localizingClosure S K → localizingClosure T (F.obj K),
      ((localizingClosure T).lift ((localizingClosure S).ι ⋙ F)
        (fun K ↦ hpres K.obj K.property)).IsEquivalence := by
  have hpres (K : C) (hK : localizingClosure S K) :
      localizingClosure T (F.obj K) := by
    exact hK ((localizingClosure T).inverseImage F)
      (inverseImageLocalizing _ _ (closureLocalizing T)) hS
  refine ⟨hpres, ?_⟩
  let H := (localizingClosure T).lift ((localizingClosure S).ι ⋙ F)
    (fun K ↦ hpres K.obj K.property)
  have himage (K : D) (hK : localizingClosure T K) :
      (localizingClosure S).map F K :=
    hK _ (imageLocalizing _ F (closureLocalizing S)) hT
  have : H.EssSurj := by
    constructor
    intro K
    obtain ⟨L, hL, ⟨e⟩⟩ := himage K.obj K.property
    exact ⟨⟨L, hL⟩, ⟨ObjectProperty.isoMk _ e⟩⟩
  exact { }

/-- The finite-Tor constructible generators correspond under the comparison functor.
Source: blueprint finite comparison, opening paragraph
(blueprint: lem-ctf-finite-comparison-generators).

Proof: apply the finite Noetherian coefficient comparison to the coefficient-sized small
site models, then transport its restricted equivalence through the constant-scalar
presentations, site equivalences, and the specified finite discrete scheme-ring
isomorphism. These transports preserve constructibility, finite Tor amplitude, and the
ambient derived comparison, yielding both generator inclusions. The empty scheme and
zero ring are included by the same equivalence argument. -/
theorem finiteComparisonGenerators_identification (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
      finiteComparisonEtaleGenerators B X K →
        finiteComparisonProEtaleGenerators B eR X
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
            X).mapDerivedCategory.obj K)) ∧
    (∀ K : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))),
      finiteComparisonProEtaleGenerators B eR X K →
        (finiteComparisonEtaleGenerators B X).map
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
            X).mapDerivedCategory K) := by
  let A := ULift.{u + 1} B
  let : IsNoetherianRing A := inferInstance
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
    HasDerivedCategory.standard _
  let E := (finiteComparisonEtaleModelRealization X A).mapDerivedCategory
  let G := (finiteComparisonProEtaleModelRealization X A).mapDerivedCategory
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  obtain ⟨D, hD, _, H, ⟨hH⟩⟩ := finiteTorComparisonNoetherian.{u, u + 1} X A
  obtain ⟨hE, hG⟩ := finiteComparisonPresentation B X eR
  obtain ⟨esquare⟩ := finiteComparisonModelDerivedSquare X A D hD
  constructor
  · intro K hK
    rw [← hE] at hK
    obtain ⟨L, hL, ⟨eL⟩⟩ := hK
    rw [← hG]
    let L' := H.functor.obj ⟨L, hL⟩
    refine ⟨L'.obj, L'.property, ⟨?_⟩⟩
    exact G.mapIso (hH.app ⟨L, hL⟩) ≪≫
      (esquare.app L).symm ≪≫ F.mapIso eL
  · intro K hK
    rw [← hG] at hK
    obtain ⟨M, hM, ⟨eM⟩⟩ := hK
    let M' := H.inverse.obj ⟨M, hM⟩
    refine ⟨E.obj M'.obj, ?_, ⟨?_⟩⟩
    · rw [← hE]
      exact ⟨M'.obj, M'.property, ⟨Iso.refl _⟩⟩
    · exact esquare.app M'.obj ≪≫ G.mapIso (hH.app M').symm ≪≫
        G.mapIso (ObjectProperty.ι _ |>.mapIso (H.counitIso.app ⟨M, hM⟩)) ≪≫ eM

/-- The finite-coefficient comparison identifies the entire etale derived category
with the localizing closure of pro-etale constructible finite-Tor objects.

Source: blueprint `sk-prop-ctf-finite-comparison`, proof steps 1--3 and 6
(blueprint: new-ctf-finite-admissible-restriction).

Proof: identify the two etale constructibility predicates using the equivalence
between finite-valued and finite-stalk constructible sheaves. The Noetherian finite-Tor
comparison, transported through the coefficient-model realization equivalences,
identifies the finite-Tor generator predicates. The unbounded comparison is exact,
fully faithful, and preserves coproducts. Its inverse image of the target closure
is localizing and contains the source generators. Its essential image on the
source closure is also localizing: fullness lifts arrows, exactness identifies
cones, and preservation of sums identifies coproducts. Minimality of both closures
therefore gives an equivalence of closures. The generation helper identifies the
source closure with the entire etale category. The restricted functor is the
original comparison followed by the subtype factorization, giving the stated
natural identification after inclusion. -/
theorem finiteAdmissibleRestriction
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type u) [CommRing A] [Finite A] (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    (∃ E : Etale.DerivedCategoryModule (ULift.{u + 1} A) X ≌
        (CategoryTheory.localizingClosure
          (DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)).FullSubcategory,
      Nonempty (E.functor ⋙ (CategoryTheory.localizingClosure
          (DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)).ι ≅
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory)) := by
  classical
  let R := ULift.{u + 1} A
  let C := ModuleCat.{u + 1} R
  let F := (comparisonUpperStar C X).mapDerivedCategory
  let S := Etale.DerivedCategory.isBoundedConstructible R X ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let T := DerivedCategory.constructibleFiniteTor C X
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  have hnil : ∃ n : ℕ, (ℓ : R) ^ n = 0 := by
    obtain ⟨n, hn⟩ := hA
    refine ⟨n, (ULift.ringEquiv : R ≃+* A).injective ?_⟩
    simpa only [map_pow, map_natCast, map_zero] using hn
  have hbc (K : Etale.DerivedCategoryModule R X) :
      Etale.DerivedCategory.isBoundedConstructible R X K ↔
        Etale.DerivedCategory.boundedConstructible C X K := by
    constructor
    · rintro ⟨hc, a, b, hab, hz⟩
      refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, ?_⟩
      · exact (_root_.DerivedCategory.isGE_iff K a).mpr (fun q hq ↦ hz q (.inl hq))
      · exact (_root_.DerivedCategory.isLE_iff K b).mpr (fun q hq ↦ hz q (.inr hq))
      · intro q
        exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc q)
    · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
      refine ⟨fun q ↦
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc q),
        min a b, b, min_le_right _ _, ?_⟩
      intro q hq
      rcases hq with hq | hq
      · exact (_root_.DerivedCategory.isGE_iff K a).mp ha q
          (lt_of_lt_of_le hq (min_le_left _ _))
      · exact (_root_.DerivedCategory.isLE_iff K b).mp hb q hq
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) R)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) R)) :=
    HasDerivedCategory.standard _
  let E := (finiteComparisonEtaleModelRealization X R).mapDerivedCategory
  let G := (finiteComparisonProEtaleModelRealization X R).mapDerivedCategory
  obtain ⟨D, hD, hmodel, _, _⟩ := finiteTorComparisonNoetherian.{u, u + 1} X R
  obtain ⟨esquare⟩ := finiteComparisonModelDerivedSquare X R D hD
  have hpro (M : ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) R)) :
      (∃ a b : ℤ, HasCoefficientModelTorAmplitude _ M a b) ↔
        _root_.DerivedCategory.finiteTorAmplitude _ (G.obj M) := by
    rw [FiniteComparisonPresentationSupport.coefficient_finite_native]
    let H := finiteComparisonProEtaleModelRealization X R
    let : H.Monoidal := proRealization_monoidal X R
    let := H.preservesFlat_of_isEquivalence
    apply exists_congr
    intro a
    apply exists_congr
    intro b
    exact (_root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff H a b M).symm
  let : (Etale.DerivedCategory.isBoundedConstructible R X).IsClosedUnderIsomorphisms :=
    etale_bounded_iso X R
  have htor (K : Etale.DerivedCategoryModule R X)
      (hc : Etale.DerivedCategory.isBoundedConstructible R X K) :
      _root_.DerivedCategory.finiteTorAmplitude _ K ↔
        _root_.DerivedCategory.finiteTorAmplitude _ (F.obj K) := by
    obtain ⟨M, ⟨eM⟩⟩ := Functor.EssSurj.mem_essImage E K
    have hcM := (coefficient_etale_bounded X R M).mpr
      ((Etale.DerivedCategory.isBoundedConstructible R X).prop_of_iso eM.symm hc)
    have hm : (∃ a b : ℤ, HasCoefficientModelTorAmplitude _ M a b) ↔
        (∃ a b : ℤ, HasCoefficientModelTorAmplitude _ (D.obj M) a b) := by
      constructor
      · rintro ⟨a, b, h⟩
        exact ⟨a, b, (hmodel M hcM a b h.1).mp h⟩
      · rintro ⟨a, b, h⟩
        exact ⟨a, b, (hmodel M hcM a b h.1).mpr h⟩
    have hleft : _root_.DerivedCategory.finiteTorAmplitude _ (E.obj M) ↔
        _root_.DerivedCategory.finiteTorAmplitude _ K :=
      ⟨fun h ↦ (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso eM h,
        fun h ↦ (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso eM.symm h⟩
    let e : G.obj (D.obj M) ≅ F.obj K := (esquare.app M).symm ≪≫ F.mapIso eM
    have hright : _root_.DerivedCategory.finiteTorAmplitude _ (G.obj (D.obj M)) ↔
        _root_.DerivedCategory.finiteTorAmplitude _ (F.obj K) :=
      ⟨fun h ↦ (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e h,
        fun h ↦ (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm h⟩
    exact hleft.symm.trans ((coefficient_etale_finiteTor X R M).symm.trans
      (hm.trans ((hpro (D.obj M)).trans hright)))
  obtain ⟨hff⟩ := finiteComparisonOrdinary_fullyFaithful R k hbase hℓ hnil X
  let : F.Full := hff.full
  let : F.Faithful := hff.faithful
  let adj := (comparisonAdjunction C X).mapDerivedCategoryRightDerivedAdjunction
  let : Coreflective F := { R := _, adj := adj }
  obtain ⟨hpres, hequiv⟩ := CategoryTheory.closureEquivalence S T F
    (fun K hK P hP hinc ↦ hinc _
      ⟨⟨K, (hbc K).mp hK.1, ⟨Iso.refl _⟩⟩, (htor K hK.1).mp hK.2⟩)
    (fun K hK ↦ by
      obtain ⟨⟨L, hL, ⟨e⟩⟩, a, b, ht⟩ := hK
      have hc := (hbc L).mpr hL
      have hf : _root_.DerivedCategory.finiteTorAmplitude _ (F.obj L) :=
        (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm ⟨a, b, ht⟩
      exact ⟨L, fun P hP hinc ↦ hinc _ ⟨hc, (htor L hc).mpr hf⟩, ⟨e⟩⟩)
  let H := (CategoryTheory.localizingClosure T).lift
    ((CategoryTheory.localizingClosure S).ι ⋙ F)
    (fun K ↦ hpres K.obj K.property)
  let : H.IsEquivalence := hequiv
  have hall (K : Etale.DerivedCategoryModule R X) :
      CategoryTheory.localizingClosure S K := by
    rw [finiteAdmissibleGeneration k hbase ℓ hℓ A hA X]
    trivial
  let L := (CategoryTheory.localizingClosure S).lift (𝟭 _) hall
  let : L.EssSurj := ⟨fun K ↦ ⟨K.obj, ⟨ObjectProperty.isoMk _ (Iso.refl _)⟩⟩⟩
  let : L.IsEquivalence := { }
  let E := L.asEquivalence.trans H.asEquivalence
  exact ⟨E, ⟨Iso.refl _⟩⟩

end CategoryTheory
end LocalizingArgument

namespace AlgebraicGeometry.ProEtale

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]
variable (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
  ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
    Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

end AlgebraicGeometry.ProEtale
