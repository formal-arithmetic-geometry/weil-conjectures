/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekLevels
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMapSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonLocal
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
public import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonClassical
public import WeilConjectures.AlgebraicGeometry.CoefficientStratifiedContinuity
public import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemOrigin
public import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemEtaleCover
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantEtaleSections
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantCounit
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Presheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Sites.Precoverage.Generates
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Data.Finite.Prod
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartCounit
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.CoefficientStratifiedEssentialImage
public import WeilConjectures.AlgebraicGeometry.CoefficientOriginOpenCover
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.AlgebraicGeometry.CoefficientOriginAffineOpenClosed
public import WeilConjectures.AlgebraicGeometry.CoefficientOriginClosedDirectImage
public import WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealizationSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonContinuity
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonRepresentableContinuity
public import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.AlgebraicGeometry.AffinePresentationSectionColimit
public import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitMaps
public import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitFactorization
public import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitEquality
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.RingTheory.IndEtaleSmallIndex
public import WeilConjectures.RingTheory.ProEtale.Etale
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonPresentationSheafification
public import WeilConjectures.AlgebraicGeometry.CoefficientClassicalModuleOrigin
public import WeilConjectures.AlgebraicGeometry.CoefficientOriginLocalizationKernel
public import WeilConjectures.AlgebraicGeometry.CoefficientFixedLocalizationKernelComparison
public import WeilConjectures.AlgebraicGeometry.CoefficientFixedClosedUnitEpi
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
public import WeilConjectures.AlgebraicGeometry.CoefficientOpenClosedKernel
public import WeilConjectures.AlgebraicGeometry.CoefficientOpenExtension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonInjectiveAcyclic
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
public import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import WeilConjectures.CategoryTheory.ModuleInverseImageAction
public import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonAffineSections
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonAffineCech
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineCechPresentation
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineCechSystem
public import WeilConjectures.AlgebraicGeometry.CechNervePresentationConstruction
public import WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.CategoryTheory.Pro.Generating
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.CategoryTheory.Sites.CechComplexRelativeLimit
public import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
public import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechExact
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.CategoryTheory.ModuleCechCriterion
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.SiteSesCechH1Surjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Constructible
public import WeilConjectures.Topology.ConstructibleIsRetrocompact
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonModuleCriteria
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor
public import WeilConjectures.AlgebraicGeometry.CoefficientClassicalSingle
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedClassicalDescent
public import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstructibilityTest
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFiniteReflection
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartReflection
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesModules
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModelSupplement
public import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonFlatPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorPairingIsIso
public import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
public import WeilConjectures.AlgebraicGeometry.RingedTopoiScalarTensorComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.CompactSupportUniformTorBound
public import WeilConjectures.AlgebraicGeometry.TowerOperationsGroundFieldRetagging
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerBound
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ComparisonTorInterval
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.AffineSpace

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerBoundsDomain
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerBoundsOperations
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerCompactBounds
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth chart tower admissibility

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
Local pairs and Uniformity (blueprint: lem-sp-tower-chart-admissibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpChartAdmissibility

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem finite_origins (T : Scheme.{u}) : origins l E T := by
  intro n M hM a b s t hab hst hcoh htor
  let A := SpTowerShriek.R l E n
  obtain ⟨L, ⟨e⟩⟩ := (finiteRing_constructibleDerived_origin T A).2.2.1 M |>.mpr
    ⟨hM.2.1, hM.1⟩
  have hplus : DerivedCategory.TStructure.t.plus L.obj := by
    obtain ⟨c, d, _, hv⟩ := L.property.2
    exact ⟨c, (DerivedCategory.isGE_iff L.obj c).2 fun i hi ↦ hv i (.inl hi)⟩
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  let R := finiteCoefficientIntrinsicRealization T A
  let ec := (Functor.mapDerivedCategoryCompIso C R).app L.obj
  have ht := (comparison_torAmplitudeIn_iff A T s t hst ⟨L.obj, hplus⟩).mpr
    (tor_of_iso T A ec (tor_of_iso T A e.symm htor))
  refine ⟨L.obj, L.property, ht, ?_, ⟨e⟩⟩
  apply ((finiteRing_constructibleDerived_origin T A).2.2.2 L.obj a b).mpr
  intro i hi
  have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj M) := by
    by_contra hn
    have hm := hcoh (show i ∈ proEtaleCohomologicalSupport M from hn)
    rcases hi with hi | hi
    · exact (not_lt_of_ge hm.1) hi
    · exact (not_lt_of_ge hm.2) hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)

private theorem scheme_facts {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    IsNoetherian T.left ∧ CompactSpace T.left ∧ QuasiSeparatedSpace T.left ∧
      (∀ U : T.left.Opens, IsNoetherian U.toScheme ∧ CompactSpace U.toScheme ∧
        QuasiSeparatedSpace U.toScheme) ∧ origins l E T.left := by
  have : IsNoetherian T.left := isNoetherian_of_locallyOfFiniteType T.hom
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, finite_origins l E T.left⟩
  intro U
  have : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set T.left))
  exact ⟨{}, inferInstance, inferInstance⟩

/-- All admissibility clauses for smooth charts, with separate uniform intervals and
without input normalization. The universally supplied sheaf-level Tate data are fixed by
their finite sheaves and normalized quotient transitions. Any such presentation gives
the same bounds and domains, since these properties are invariant under isomorphism.

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
Local pairs and Uniformity (blueprint: lem-sp-tower-chart-admissibility).

Proof:
1. Finite type over a field is Noetherian. Its opens are Noetherian and hence qcqs.
   The fixed coefficient quotient is finite and therefore Noetherian. For each
   finite level use finiteRing_constructibleDerived_origin to obtain an etale
   bounded constructible complex. Its exact comparison reflects the prescribed
   cohomological interval; comparison_torAmplitudeIn_iff reflects the Tor interval.
   No compatibility between these independent origins is imposed.
2. Apply domain_of_level_bounds to recover the actual ordinary tower domain from
   uniform bounds and the independent finite origins of step 1.
3. elementary_tower_bounds preserves both intervals under a single inverse image
   and a specified Tate tensor; a shift subtracts its index from all endpoints.
   Compose these laws for the chart, and induct over the ordered affine stages.
   At each successor the shift subtracts two. Apply step 2 to each resulting tower.
4. Open immersions are etale; their relative dimension is zero. Relative dimensions
   add under composition and survive arbitrary base change. Thus restrictions of
   f remain smooth of dimension d, including after arbitrary geometric points;
   the standard affine projection is smooth of dimension one.
5. smooth_tower_compact_bounds applies the existing uniform compact-support theorem
   to a single smooth map and uses the canonical evaluation and open-adjunction
   comparisons. It gives finite output bounds [s,t+2d]. Step 2 gives the output
   domain. Apply this argument to the restrictions, to each affine projection with
   dimension one, and to each open or etale extension with dimension zero.
-/
theorem tower_chart_admissibility
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hlp : l ≠ p)
    (base : SpTowerShriek.Base l E) (ops : SpTowerShriek.Operations l E base)
    (X Y : Over (Spec (.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (K : SpTowerShriek.D l E Y.left) (a b s t : ℤ) (_hab : a ≤ b) (_hst : s ≤ t)
    (_hK : bounds l E Y.left K a b s t) :
    ∀ w : ∀ T : Over (Spec (.of k)), Twists l E T.left,
      (∀ T : Over (Spec (.of k)),
        IsSeparated T.hom → LocallyOfFiniteType T.hom → QuasiCompact T.hom →
        IsNoetherian T.left ∧ CompactSpace T.left ∧ QuasiSeparatedSpace T.left ∧
        (∀ U : T.left.Opens,
          IsNoetherian U.toScheme ∧ CompactSpace U.toScheme ∧
          QuasiSeparatedSpace U.toScheme) ∧ origins l E T.left) ∧
      (∀ n : ℕ, IsNoetherianRing (SpTowerShriek.R l E n) ∧
        Finite (SpTowerShriek.R l E n)) ∧
      domain l E base Y.left K ∧
      intermediate l E base ops Y w K d a b s t ∧
      (∀ (U : X.left.Opens)
        (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) Y.left),
        Etale e → IsSeparated e → LocallyOfFiniteType e → QuasiCompact e →
        e ≫ (AffineSpace (ULift.{u} (Fin d)) Y.left ↘ Y.left) = U.ι ≫ f.left →
        bounds l E U.toScheme
          (chart l E base ops e (AffineSpace (ULift.{u} (Fin d)) Y.left ↘ Y.left)
            (w (Over.mk (U.ι ≫ X.hom))) K d)
          (a - 2 * (d : ℤ)) (b - 2 * (d : ℤ))
          (s - 2 * (d : ℤ)) (t - 2 * (d : ℤ)) ∧
        domain l E base U.toScheme
          (chart l E base ops e (AffineSpace (ULift.{u} (Fin d)) Y.left ↘ Y.left)
            (w (Over.mk (U.ι ≫ X.hom))) K d) ∧
        ∀ c : Compactification e, compact l E base ops c 0) ∧
      (∀ U : X.left.Opens,
        SmoothOfRelativeDimension d (U.ι ≫ f.left) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y.left),
          SmoothOfRelativeDimension d (pullback.snd (U.ι ≫ f.left) y)) ∧
        (∀ c : Compactification (U.ι ≫ f.left), compact l E base ops c d) ∧
        ∀ c : Compactification U.ι, compact l E base ops c 0) := by
  classical
  have hX := (scheme_facts l E X).1
  have hY := (scheme_facts l E Y).1
  have hdom (T : Over (Spec (.of k))) [IsNoetherian T.left]
      (C : SpTowerShriek.D l E T.left) (a b s t : ℤ)
      (hab : a ≤ b) (hst : s ≤ t) (hC : bounds l E T.left C a b s t) :
      domain l E base T.left C :=
    domain_of_level_bounds l E base T.left (finite_origins l E T.left)
      C a b s t hab hst hC
  obtain ⟨hpull, htwist, hshift⟩ := elementary_tower_bounds l E p k _hlp base ops
  have hcpt (Z T : Over (Spec (.of k)))
      [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
      [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
      (g : Z ⟶ T) (r : ℕ) [SmoothOfRelativeDimension r g.left]
      (c : Compactification g.left) : compact l E base ops c r := by
    have := (scheme_facts l E T).1
    intro C a b s t hab hst hC
    have hb := smooth_tower_compact_bounds l E p k _hlp base ops Z T g r c
      C a b s t hab hst hC
    exact ⟨hb, hdom T _ s (t + 2 * (r : ℤ)) s (t + 2 * (r : ℤ))
      (by omega) (by omega) hb⟩
  intro w
  refine ⟨?_, ?_, hdom Y K a b s t _hab _hst _hK, ?_, ?_, ?_⟩
  · intro T hs hf hq
    exact scheme_facts l E T
  · intro n
    exact ⟨inferInstance, inferInstance⟩
  · intro r hr
    let V (j : ℕ) : Over (Spec (.of k)) :=
      Over.mk ((space Y.left j ↘ Y.left) ≫ Y.hom)
    have hVs (j : ℕ) : IsSeparated (V j).hom :=
      inferInstanceAs (IsSeparated ((space Y.left j ↘ Y.left) ≫ Y.hom))
    have hVf (j : ℕ) : LocallyOfFiniteType (V j).hom :=
      inferInstanceAs (LocallyOfFiniteType ((space Y.left j ↘ Y.left) ≫ Y.hom))
    have hVq (j : ℕ) : QuasiCompact (V j).hom :=
      inferInstanceAs (QuasiCompact ((space Y.left j ↘ Y.left) ≫ Y.hom))
    have hV (j : ℕ) : IsNoetherian (V j).left := (scheme_facts l E (V j)).1
    have hv (j : ℕ) : bounds l E (space Y.left j)
        ((SpTowerShriek.pull l E base (ops.geometry (space Y.left j ↘ Y.left))).obj K)
        a b s t :=
      hpull (V j) Y (Over.homMk (space Y.left j ↘ Y.left) rfl) K a b s t _hK
    have ht (j : ℕ) := htwist (V j) (w (V j)) _ j a b s t (hv j)
    have hs (j : ℕ) := hshift _ _ (2 * (j : ℤ)) a b s t (ht j)
    have hstage (j : ℕ) : bounds l E (space Y.left j) (stage l E base ops Y w K j)
        (a - 2 * (j : ℤ)) (b - 2 * (j : ℤ))
        (s - 2 * (j : ℤ)) (t - 2 * (j : ℤ)) := by
      induction j with
      | zero => simpa [stage] using hv 0
      | succ j ih =>
        have hp := hpull (V (j + 1)) (V j)
          (Over.homMk (projection Y.left j) (by
            dsimp [V, projection]
            rw [← Category.assoc, AffineSpace.reindex_over]))
          _ _ _ _ _ ih
        have hh := htwist (V (j + 1)) (w (V (j + 1))) _ 1 _ _ _ _ hp
        have hsh := hshift _ _ 2 _ _ _ _ hh
        change bounds l E (space Y.left (j + 1)) (stage l E base ops Y w K (j + 1))
          ((a - 2 * (j : ℤ)) - 2) ((b - 2 * (j : ℤ)) - 2)
          ((s - 2 * (j : ℤ)) - 2) ((t - 2 * (j : ℤ)) - 2) at hsh
        simpa only [V, Over.mk_left, Over.homMk_left, stage, Nat.cast_add,
          Nat.cast_one, mul_add, mul_one, sub_sub] using hsh
    have hd0 : a - 2 * (r : ℤ) ≤ b - 2 * (r : ℤ) := by omega
    have hd1 : s - 2 * (r : ℤ) ≤ t - 2 * (r : ℤ) := by omega
    refine ⟨hv r, hdom (V r) _ a b s t _hab _hst (hv r), ht r,
      hdom (V r) _ a b s t _hab _hst (ht r), hs r,
      hdom (V r) _ _ _ _ _ hd0 hd1 (hs r), hstage r,
      hdom (V r) _ _ _ _ _ hd0 hd1 (hstage r), ?_, ?_⟩
    · intro W c
      have : IsNoetherian (space Y.left r) := hV r
      let Z : Over (Spec (.of k)) := Over.mk (W.ι ≫ (V r).hom)
      have : IsSeparated Z.hom := inferInstanceAs (IsSeparated (W.ι ≫ (V r).hom))
      have : LocallyOfFiniteType Z.hom :=
        inferInstanceAs (LocallyOfFiniteType (W.ι ≫ (V r).hom))
      have : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (W.ι ≫ (V r).hom))
      let g : Z ⟶ V r := Over.homMk W.ι rfl
      have : SmoothOfRelativeDimension 0 g.left :=
        inferInstanceAs (SmoothOfRelativeDimension 0 W.ι)
      exact hcpt Z (V r) g 0 c
    · intro _
      have hp := hpull (V (r + 1)) (V r)
        (Over.homMk (projection Y.left r) (by
          dsimp [V, projection]
          rw [← Category.assoc, AffineSpace.reindex_over])) _ _ _ _ _ (hstage r)
      have hh := htwist (V (r + 1)) (w (V (r + 1))) _ 1 _ _ _ _ hp
      refine ⟨hp, hdom (V (r + 1)) _ _ _ _ _ hd0 hd1 hp,
        hh, hdom (V (r + 1)) _ _ _ _ _ hd0 hd1 hh, ?_⟩
      intro c
      let g : V (r + 1) ⟶ V r := Over.homMk (projection Y.left r) (by
        dsimp [V, projection]
        rw [← Category.assoc, AffineSpace.reindex_over])
      have : SmoothOfRelativeDimension 1 g.left :=
        AffineSpace.smoothOfRelativeDimension_reindex_succ r Y.left
      exact hcpt (V (r + 1)) (V r) g 1 c
  · intro U e he hsep hft hqc hfac
    let Z : Over (Spec (.of k)) := Over.mk (U.ι ≫ X.hom)
    let V : Over (Spec (.of k)) :=
      Over.mk ((AffineSpace (ULift.{u} (Fin d)) Y.left ↘ Y.left) ≫ Y.hom)
    have hZs : IsSeparated Z.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
    have hZf : LocallyOfFiniteType Z.hom :=
      inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
    have hZq : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (U.ι ≫ X.hom))
    have hZ := (scheme_facts l E Z).1
    have hVs : IsSeparated V.hom :=
      inferInstanceAs (IsSeparated ((space Y.left d ↘ Y.left) ≫ Y.hom))
    have hVf : LocallyOfFiniteType V.hom :=
      inferInstanceAs (LocallyOfFiniteType ((space Y.left d ↘ Y.left) ≫ Y.hom))
    have hVq : QuasiCompact V.hom :=
      inferInstanceAs (QuasiCompact ((space Y.left d ↘ Y.left) ≫ Y.hom))
    have hV := (scheme_facts l E V).1
    let pe : V ⟶ Y := Over.homMk _ rfl
    let ee : Z ⟶ V := Over.homMk e (by
      dsimp [Z, V]
      rw [← Category.assoc, hfac, Category.assoc, Over.w f])
    have hp := hpull V Y pe K a b s t _hK
    have hp' := hpull Z V ee _ a b s t hp
    have ht := htwist Z (w Z) _ d a b s t hp'
    have hs := hshift _ _ (2 * (d : ℤ)) a b s t ht
    refine ⟨hs, hdom Z _ _ _ _ _ (by omega) (by omega) hs, ?_⟩
    intro c
    have : SmoothOfRelativeDimension 0 ee.left :=
      (Etale.iff_smoothOfRelativeDimension_zero e).mp he
    exact hcpt Z V ee 0 c
  · intro U
    let Z : Over (Spec (.of k)) := Over.mk (U.ι ≫ X.hom)
    have hZs : IsSeparated Z.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
    have hZf : LocallyOfFiniteType Z.hom :=
      inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
    have hZq : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (U.ι ≫ X.hom))
    have hsm : SmoothOfRelativeDimension d (U.ι ≫ f.left) := by
      simpa using (inferInstance : SmoothOfRelativeDimension (0 + d) (U.ι ≫ f.left))
    refine ⟨hsm, ?_, ?_, ?_⟩
    · intro Ω _ _ y
      infer_instance
    · intro c
      let g : Z ⟶ Y := Over.homMk (U.ι ≫ f.left) (by
        simp only [Z, Over.mk_hom, Category.assoc, Over.w f])
      have : SmoothOfRelativeDimension d g.left := hsm
      exact hcpt Z Y g d c
    · intro c
      let g : Z ⟶ X := Over.homMk U.ι rfl
      have : SmoothOfRelativeDimension 0 g.left :=
        inferInstanceAs (SmoothOfRelativeDimension 0 U.ι)
      exact hcpt Z X g 0 c

end AlgebraicGeometry.ProEtale.SpChartAdmissibility
