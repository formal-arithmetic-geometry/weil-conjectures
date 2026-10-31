/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import WeilConjectures.CategoryTheory.NativeHomSourceShiftData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.Algebra.Homology.RingedScalarHomExact
import WeilConjectures.Algebra.Homology.ScalarHomComparisonTower
import WeilConjectures.Algebra.Homology.ScalarHomTensorCoherence
import WeilConjectures.Algebra.Homology.ScalarInternalHomAdjunction
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissageSupplement
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleHomSingle
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
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
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMapSupplement
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructible
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
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
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantCounit
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
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
import WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealizationSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonContinuity
import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonRepresentableContinuity
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Adjunction.Limits
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
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.SiteSesCechH1Surjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Constructible
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
import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksBlueprint
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModelSupplement
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
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
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
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
import WeilConjectures.CategoryTheory.RingedSiteDualityMaps
import WeilConjectures.CategoryTheory.RingedSitePerfectDuality
import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.CartesianCoefficientsFiniteFree
import WeilConjectures.AlgebraicGeometry.ConstructibleInternalHomContinuity
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientModelComparison
import WeilConjectures.AlgebraicGeometry.IntegralGeneralLfpHomInversion
import WeilConjectures.AlgebraicGeometry.PrincipalReductionDerivedNormalization
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.AlgebraicGeometry.PrincipalConeTensorNormalization
import WeilConjectures.Algebra.Homology.ReductionIsoShift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.AlgebraicGeometry.PrincipalTensorScalarExtension
import WeilConjectures.Algebra.Homology.InternalKFlatScalarTowerRealizationSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwists
import WeilConjectures.AlgebraicGeometry.QlbarInternalHomCoefficientComparison
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import all WeilConjectures.AlgebraicGeometry.IntegralCoefficientExtComparison

/-! # Constructible internal Hom and coefficient comparison

Source: Bhatt--Scholze, Lemmas 6.7.13, 6.8.13, Proposition 6.8.14(2),
Remark 6.8.15; Hemo--Richarz--Scholbach, Theorem 7.7, Lemma 7.9, Remark 7.10.
The closure has the finite-subextension-valued condensed structure.
(blueprint: lem-per-constructible-coefficient-hom-comparison)
-/

public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

variable (X : Scheme.{u})
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

/-- The ordinary ambient derived category over the pulled-back coefficient ring.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev D (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj R X))

/-- The recorded finite-constant-local-model bounded constructibility predicate.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev bc (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] := constantModelBoundedConstructible R X

/-- Ordinary derived internal Hom, with no completion or restriction to chosen models.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev hom (K L : D X R) : D X R :=
  ((CondensedRing.derivedHom R X).obj (op K)).obj L

/-- The counit of the recorded ordinary derived tensor--Hom adjunction.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def evaluation (K L : D X R) : K ⊗ hom X K L ⟶ L :=
  (CondensedRing.derivedTensorHomAdjunction R K).counit.app L

/-- Derived scalar extension along the actual pulled-back ring map.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev scalar (a : R ⟶ S) [IsMonHom a] : D X R ⥤ D X S :=
  (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor

/-- The scalar shift is the canonical left-adjoint mate of exact scalar restriction.
Source: Stacks 08JC; the native derived change-of-rings adjunction
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
instance scalarShift (a : R ⟶ S) [IsMonHom a] : (scalar X a).CommShift ℤ :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).leftAdjointCommShift ℤ

/-- The canonical strong monoidal structure obtained by deriving balanced scalar tensor.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose, instance_reducible]
def scalarMonoidal (a : R ⟶ S) [IsMonHom a] : (scalar X a).Monoidal :=
  letI := CondensedRing.internalScalarMonoidal a X
  (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorMonoidal

/-- The balanced tensorator; it is defined also for nonflat finite quotient maps.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def tensorator (a : R ⟶ S) [IsMonHom a] (K L : D X R) :
    (scalar X a).obj K ⊗ (scalar X a).obj L ⟶ (scalar X a).obj (K ⊗ L) :=
  letI := scalarMonoidal X a
  Functor.LaxMonoidal.μ (scalar X a) K L

/-- The actual scalar--Hom map: transpose of tensorator followed by scalar evaluation.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def comparison (a : R ⟶ S) [IsMonHom a] (K L : D X R) :
    (scalar X a).obj (hom X K L) ⟶
      hom X ((scalar X a).obj K) ((scalar X a).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction S ((scalar X a).obj K)).homEquiv _ _
    (tensorator X a K (hom X K L) ≫ (scalar X a).map (evaluation X K L))

/-- The actual relative bidual arrow, transposing evaluation after the Koszul symmetry.
This definition makes no assertion of invertibility.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def bidual (K W : D X R) : K ⟶ hom X (hom X K W) W :=
  MonoidalClosed.curry ((β_ (hom X K W) K).hom ≫ evaluation X K W)

/-- Composition of internal morphisms, transposed from the two evaluation maps.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def composition (K L M : D X R) :
    hom X K L ⊗ hom X L M ⟶ hom X K M :=
  MonoidalClosed.curry
    ((α_ K (hom X K L) (hom X L M)).inv ≫
      (evaluation X K L ⊗ₘ 𝟙 (hom X L M)) ≫ evaluation X L M)

/-- Tensoring internal morphisms. Its middle interchange is the native Koszul braiding.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def tensorHom (K L P Q : D X R) :
    hom X K L ⊗ hom X P Q ⟶ hom X (K ⊗ P) (L ⊗ Q) :=
  MonoidalClosed.curry
    (tensorμ K P (hom X K L) (hom X P Q) ≫
      (evaluation X K L ⊗ₘ evaluation X P Q))

/-- The integral coefficient ring in the spectral presentation used by derived completion.
The universe lift changes only its presentation, not the embedded coefficient field.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev integral (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  DerivedNakayama.integerRing.{u} ℓ (ULift.{u} E.val)

/-- The canonical continuous integer-ring isomorphism, induced by the lifted inclusion.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
def integralIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Profinite.padicIntegersRingObj.{u} ℓ E.val ≅ integral.{u} ℓ E :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
      (AlgebraicGeometry.ProEtale.integerRingSheafIso ℓ E)

/-- The canonical integer comparison preserves multiplication and the unit.
Source: the continuous ring-map construction in IntegralCoefficientExtComparison
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
instance integralIso_isMonHom (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : IsMonHom (integralIso.{u} ℓ E).hom := by
  dsimp [integralIso]
  infer_instance

/-- The actual inclusion of integral coefficients into the embedded finite field,
transported along the canonical spectral/embedded integer isomorphism.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev integralToField (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    integral.{u} ℓ E ⟶ Profinite.continuousMapRingObj.{u} E.val :=
  (integralIso ℓ E).inv ≫ padicIntegersRingObjToContinuousMapRingObj ℓ E

/-- The quotient at exponent n+1; hence index zero means the first positive reduction.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev finite (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  DerivedNakayama.quotientRing.{u} ℓ (ULift.{u} E.val) (n + 1)

/-- The actual uniformizer-power quotient map, with no arbitrary choice of scalar map.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev reductionMap (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  DerivedNakayama.reductionRing.{u} ℓ (ULift.{u} E.val) (n + 1)

/-- The signed Tate line in the native module encoding, placed in degree zero.
This uses the recorded signed-power construction and its section-module equivalence.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def signedLine (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (n : ℤ) : D X R :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((InternalAbelianSheafModule.sectionModuleEquivalence
      (Scheme.ProEt.topology X) (condensedRingObj R X)).inverse.obj
        (spSignedTwist X _ L n))

/-- The actual integral Tate line, transported to the completion coefficient presentation.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def integralLine (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  (Mod.comap (coefficientMap (integralIso.{u} ℓ E).inv X)).obj (spIntegralTwist X ℓ E)

/-- Closure under ordinary internal Hom in the full bounded constructible category.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def HomClosed (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] : Prop :=
  ∀ K L : D X R, bc X R K → bc X R L → bc X R (hom X K L)

/-- Bounded constructible finite-Tor origin on the actual small étale site.
The encoding is constrained by its constant-section normalization, not arbitrary.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def FiniteEtaleOrigin (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)
    (K : D X (finite.{u} ℓ E n)) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
  letI := AdicCompletion.finiteTopology ℓ (ULift.{u} E.val) (n + 1)
  ∃ enc : FiniteDiscreteOrdinary.Encoding
      (Padic.coefficientExtensionRing ℓ (ULift.{u} E.val) (n + 1)) X,
    ∃ J : DerivedCategory (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing ℓ (ULift.{u} E.val) (n + 1))))),
      DerivedCategory.TStructure.t.bounded J ∧
      (∀ i : ℤ, Scheme.IsConstructibleSheaf ((DerivedCategory.homologyFunctor _ i).obj J)) ∧
      DerivedCategory.finiteTorAmplitude _ J ∧
      Nonempty ((comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing ℓ (ULift.{u} E.val) (n + 1)))) X).mapDerivedCategory.obj
            J ≅
            enc.fixedDerived.functor.obj K)

/-- Integral completeness means the recorded canonical completion map is invertible.
Every positive finite reduction has the exact constructibility, Tor and origin clauses.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def IntegralAssertions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : Prop :=
  ∀ K : D X (integral.{u} ℓ E), bc X (integral ℓ E) K →
    IsDerivedComplete ℓ (ULift.{u} E.val) X K ∧
    ∀ n : ℕ,
      bc X (finite ℓ E n) ((scalar X (reductionMap ℓ E n)).obj K) ∧
      DerivedCategory.finiteTorAmplitude _ ((scalar X (reductionMap ℓ E n)).obj K) ∧
      FiniteEtaleOrigin X ℓ E n ((scalar X (reductionMap ℓ E n)).obj K)

/-- Evaluation, Koszul symmetry, composition and the actual arbitrary-target bidual
commute with the specified scalar comparison. There is no bidual invertibility clause.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def EvaluationCoherence (a : R ⟶ S) [IsMonHom a] : Prop :=
  (∀ K L : D X R,
    tensorator X a K (hom X K L) ≫ (scalar X a).map (evaluation X K L) =
      (𝟙 ((scalar X a).obj K) ⊗ₘ comparison X a K L) ≫
        evaluation X ((scalar X a).obj K) ((scalar X a).obj L)) ∧
  (∀ K L : D X R,
    tensorator X a K L ≫ (scalar X a).map (β_ K L).hom =
      (β_ ((scalar X a).obj K) ((scalar X a).obj L)).hom ≫ tensorator X a L K) ∧
  (∀ K L M : D X R,
    tensorator X a (hom X K L) (hom X L M) ≫
        (scalar X a).map (composition X K L M) ≫ comparison X a K M =
      (comparison X a K L ⊗ₘ comparison X a L M) ≫
        composition X ((scalar X a).obj K) ((scalar X a).obj L) ((scalar X a).obj M)) ∧
  (∀ K W : D X R, bc X R K → bc X R W →
    (scalar X a).map (bidual X K W) ≫ comparison X a (hom X K W) W =
      bidual X ((scalar X a).obj K) ((scalar X a).obj W) ≫
        ((CondensedRing.derivedHom S X).map (comparison X a K W).op).app
          ((scalar X a).obj W))

/-- The target-Hom shift is the right-adjoint mate of the native derived tensor shift.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def targetShift (K L : D X R) (n : ℤ) :
    hom X K (L⟦n⟧) ≅ (hom X K L)⟦n⟧ :=
  letI := (ihom.adjunction K).rightAdjointCommShift ℤ
  ((ihom K).commShiftIso n).app L

/-- Compatibility with both integer shifts, including the signed opposite exact
source shift. The same Koszul shift conventions are used on both sides.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def ShiftCoherence (a : R ⟶ S) [IsMonHom a] : Prop :=
  (∀ (K L : D X R) (n : ℤ),
    (scalar X a).map (targetShift X K L n).hom ≫
        ((scalar X a).commShiftIso n).hom.app (hom X K L) ≫
          (shiftFunctor (D X S) n).map (comparison X a K L) =
      comparison X a K (L⟦n⟧) ≫
        (ihom ((scalar X a).obj K)).map (((scalar X a).commShiftIso n).hom.app L) ≫
          (targetShift X ((scalar X a).obj K) ((scalar X a).obj L) n).hom) ∧
  (∀ (K L : D X R) (n : ℤ),
    (scalar X a).map (siteHomSignedSourceComponent L n (op K)) ≫
        ((scalar X a).commShiftIso n).hom.app (hom X K L) ≫
          (shiftFunctor (D X S) n).map (comparison X a K L) =
      comparison X a (K⟦-n⟧) L ≫
        ((CondensedRing.derivedHom S X).map
          (((scalar X a).commShiftIso (-n)).inv.app K).op).app ((scalar X a).obj L) ≫
          siteHomSignedSourceComponent ((scalar X a).obj L) n (op ((scalar X a).obj K)))

/-- Naturality in both inputs, as an equality of actual internal-sheaf morphisms.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def NaturalComparison (a : R ⟶ S) [IsMonHom a] : Prop :=
  ∀ (K K' L L' : D X R) (f : K' ⟶ K) (g : L ⟶ L'),
    (scalar X a).map (((CondensedRing.derivedHom R X).map f.op).app L ≫
      ((CondensedRing.derivedHom R X).obj (op K')).map g) ≫ comparison X a K' L' =
    comparison X a K L ≫
      ((CondensedRing.derivedHom S X).map ((scalar X a).map f).op).app
        ((scalar X a).obj L) ≫
      ((CondensedRing.derivedHom S X).obj (op ((scalar X a).obj K'))).map
        ((scalar X a).map g)

/-- Full-category preservation, invertibility and coherence of scalar--Hom comparison.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def ScalarAssertions (a : R ⟶ S) [IsMonHom a] : Prop :=
  (∀ K : D X R, bc X R K → bc X S ((scalar X a).obj K)) ∧
  (∀ K L : D X R, bc X R K → bc X R L → IsIso (comparison X a K L)) ∧
  EvaluationCoherence X a ∧ ShiftCoherence X a ∧ NaturalComparison X a

/-- The canonical successive-scalar identification, defined by the existing derived
change-of-rings adjunction and its normalized restriction composition.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def scalarTower
    {T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj T] [IsCommMonObj T]
    (a : R ⟶ S) [IsMonHom a] (b : S ⟶ T) [IsMonHom b] :
    scalar X (a ≫ b) ≅ scalar X a ⋙ scalar X b :=
  Mod.derivedExtendScalarsCompIso (coefficientMap a X) (coefficientMap b X)
    (coefficientMap (a ≫ b) X) (coefficientMap_comp a b X).symm

/-- Direct-versus-successive scalar comparison, including the actual canonical
composition transport, rather than existence of some identifying isomorphism.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def TowerCoherence
    {T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj T] [IsCommMonObj T]
    (a : R ⟶ S) [IsMonHom a] (b : S ⟶ T) [IsMonHom b] : Prop :=
  ∀ K L : D X R,
    (scalarTower X a b).hom.app (hom X K L) ≫
        (scalar X b).map (comparison X a K L) ≫
        comparison X b ((scalar X a).obj K) ((scalar X a).obj L) =
      comparison X (a ≫ b) K L ≫
        ((CondensedRing.derivedHom T X).map ((scalarTower X a b).inv.app K).op).app
          ((scalar X (a ≫ b)).obj L) ≫
        ((CondensedRing.derivedHom T X).obj
          (op ((scalar X b).obj ((scalar X a).obj K)))).map
            ((scalarTower X a b).hom.app L)

/-- The identity-coefficient identification induced by the scalar-unit adjunction.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def scalarIdentity
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] : scalar X (𝟙 R) ≅ 𝟭 (D X R) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (𝟙 R) X)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso
        (Mod.comapCongr (coefficientMap_id X) ≪≫ Mod.comapId (condensedRingObj R X)) ≪≫
          Functor.mapDerivedCategoryIdIso _).symm)

/-- The exact identity normalization of the evaluation-transpose comparison.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def IdentityCoherence
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] : Prop :=
  ∀ K L : D X R,
    comparison X (𝟙 R) K L ≫
        ((CondensedRing.derivedHom R X).map ((scalarIdentity X R).inv.app K).op).app
          ((scalar X (𝟙 R)).obj L) ≫
        ((CondensedRing.derivedHom R X).obj (op K)).map ((scalarIdentity X R).hom.app L) =
      (scalarIdentity X R).hom.app (hom X K L)

/-- The native derived pullback along a scheme isomorphism, with its canonical monoidal
structure. The definition uses the actual inverse-image functor, not an abstract equivalence.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev pull {Y : Scheme.{u}}
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (e : X ≅ Y) : D Y R ⥤ D X R :=
  (CondensedRing.upperStar R e.hom).leftDerivedFunctor

/-- The evaluation-transpose internal-Hom comparison for the actual scheme pullback.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def pullComparison {Y : Scheme.{u}}
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (e : X ≅ Y) (K L : D Y R) :
    (pull X R e).obj (hom Y K L) ⟶ hom X ((pull X R e).obj K) ((pull X R e).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction R ((pull X R e).obj K)).homEquiv _ _
    (Functor.LaxMonoidal.μ (pull X R e) K (hom Y K L) ≫
      (pull X R e).map (evaluation Y K L))

/-- The normalized scalar/pullback interchange, valid even for nonflat quotients.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev pullScalar {Y : Scheme.{u}} (a : R ⟶ S) [IsMonHom a] (e : X ≅ Y) :
    pull X R e ⋙ scalar X a ≅ scalar Y a ⋙ pull X S e :=
  CondensedRing.derivedUpperStarExtendScalarsIso a e.hom

/-- Commutation with scheme isomorphisms as the actual square on internal Hom.
It retains both first-input contravariance and the specified scalar/pullback interchange.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def SchemeCoherence (a : R ⟶ S) [IsMonHom a] : Prop :=
  ∀ (Y : Scheme.{u}) (e : X ≅ Y) (K L : D Y R),
    (pullScalar X a e).hom.app (hom Y K L) ≫
        (pull X S e).map (comparison Y a K L) ≫
        pullComparison X S e ((scalar Y a).obj K) ((scalar Y a).obj L) =
      (scalar X a).map (pullComparison X R e K L) ≫
        comparison X a ((pull X R e).obj K) ((pull X R e).obj L) ≫
        ((CondensedRing.derivedHom S X).map ((pullScalar X a e).inv.app K).op).app
          ((scalar X a).obj ((pull X R e).obj L)) ≫
        ((CondensedRing.derivedHom S X).obj
          (op ((pull X S e).obj ((scalar Y a).obj K)))).map
            ((pullScalar X a e).hom.app L)

/-- Tensor-Hom compatibility. Specializing P and Q to the constructed signed Tate
lines gives the Tate-twist square, with exactly the balanced evaluations and Koszul signs.
It also applies to their finite quotient reductions.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def TensorCoherence (a : R ⟶ S) [IsMonHom a] : Prop :=
  ∀ K L P Q : D X R,
    tensorator X a (hom X K L) (hom X P Q) ≫
        (scalar X a).map (tensorHom X K L P Q) ≫ comparison X a (K ⊗ P) (L ⊗ Q) ≫
        ((CondensedRing.derivedHom S X).map (tensorator X a K P).op).app
          ((scalar X a).obj (L ⊗ Q)) =
      (comparison X a K L ⊗ₘ comparison X a P Q) ≫
        tensorHom X ((scalar X a).obj K) ((scalar X a).obj L)
          ((scalar X a).obj P) ((scalar X a).obj Q) ≫
        ((CondensedRing.derivedHom S X).obj
          (op ((scalar X a).obj K ⊗ (scalar X a).obj P))).map (tensorator X a L Q)

/-- All coherence clauses for a specified actual coefficient map. Tower coherence
is formal even if the second comparison is not invertible; the displayed field and quotient
maps themselves are required to be invertible on the full constructible categories.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def CoherentScalarAssertions (a : R ⟶ S) [IsMonHom a] : Prop :=
  ScalarAssertions X a ∧ TensorCoherence X a ∧ SchemeCoherence X a ∧
  IdentityCoherence X R ∧ IdentityCoherence X S ∧
  ∀ (T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj T] [IsCommMonObj T] (b : S ⟶ T) [IsMonHom b], TowerCoherence X a b

/-- For the actual Tate lines the tensor-Hom comparison is invertible. Thus the
preceding tensor square is the signed Tate compatibility, rather than just an equation
after forgetting the line. Both positive and negative powers and degree zero are included.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def TateAssertions
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (line : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) : Prop :=
  (∀ n : ℤ, bc X R (signedLine X R line n)) ∧
  ∀ (K L : D X R), bc X R K → bc X R L → ∀ m n : ℤ,
    IsIso (tensorHom X K L (signedLine X R line m) (signedLine X R line n))

/-- Constructible ordinary internal Hom, coefficient comparisons, integral and finite-field
models, and evaluation-normalized coherence over a perfect field in dimensions zero and one.
The algebraic closure is the finite-subextension-valued condensed ring, with no completion.

Source: Bhatt--Scholze, Lemmas 6.7.13 and 6.8.13, Proposition 6.8.14(2), Remark 6.8.15;
Hemo--Richarz--Scholbach, Theorem 7.7, Lemma 7.9, Remark 7.10; blueprint
`thm-a1-curve-perverse-heart`, Step 3 and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).

Proof:
1. Since $\operatorname{Spec}k$ is Noetherian, finite type makes $X$ Noetherian by
[lem-weil-pbc-finite-type-over-noetherian]. Work on a small pro-étale site in the module universe.
The equivalence [lem-sfb-module-object-ringed-site-derived-comparison] identifies the specified
ordinary module-object tensor, internal Hom and evaluation with the ringed-site operations. For
$O,E,F,\Omega$, [lem-sfb-adic-constructibility-predicate-comparison] identifies finite constant
local models with the stratified finite-presentation predicate, in the same ambient derived
category. Thus [lem-sfb-bounded-constructible-triangulated-finiteness] gives a full replete
triangulated category $C_\Lambda$ for each of these coefficients. These identifications impose no
completeness hypothesis and use the finite-subextension-valued $\Omega$.

2. Fix $\Lambda\in\{O,E,F,\Omega\}$. For constructible sheaves $A,B$, [lem-sfb-dc-hom-single]
gives $R\mathcal Hom_\Lambda(A[0],B[0])\in C_\Lambda$: its hypotheses are separated finite type
over a field and $\operatorname{char}k\ne\ell$, all present here, including characteristic zero.
By [lem-weil-pbc-ringed-internal-hom-exact-restriction], internal Hom sends triangles in either
variable to triangles and respects integer shifts. For fixed $A$, the property $R\mathcal
Hom_\Lambda(A[0],L)\in C_\Lambda$ is therefore triangulated and contains every constructible
$B[0]$. Apply [lem-sfb-dc-module-devissage] to obtain it for every $L\in C_\Lambda$. Now fix such
$L$ and apply that devissage to the triangulated property $R\mathcal Hom_\Lambda(K,L)\in
C_\Lambda$ in $K$, using contravariant exactness. Its degree-zero cases were just proved; hence it
holds for all $K\in C_\Lambda$. The induction is the finite Postnikov induction of that node, with
zero as base and the highest nonzero cohomology sheaf as the next quotient. In particular
$H=R\mathcal Hom_{O_X}(K,L)$ is bounded constructible.

3. Apply [lem-sfb-internal-integral-criterion-forward] to each $M=K,L,H$ from Step 2. It gives
derived $\pi$-completeness in the precise canonical-map sense of the item and bounded
constructibility of $M_1$. Choose a finite interval containing the cohomology of $M_1$. Then
[sk-lem-integral-finite-levels] gives bounded constructibility and finite Tor amplitude for every
$M_n$ over $(O/\pi^n)_X$. Since $O/\pi^n$ is a finite discrete Noetherian ring,
[lem-pe-finite-coefficient-model-comparison] identifies this constructibility with the ordinary
finite-stalk predicate. The scheme $X$ is qcqs, so [sk-thm-pe-constructible-comparison] supplies
an étale-origin object, and [det-pe-finite-tor-comparison-noetherian] makes its Tor amplitude
finite on the étale site as well. Thus all three objects have the required finite-Tor étale
reductions. The completeness assertion is about the original ambient objects, not about replacing
them by their completions.

4. Put $R=O_X$, $S=(O/\pi^n)_X$ with $n\ge1$, and $P=\operatorname{Res}_R S$. Applying
[lem-pe-principal-reduction-derived-normalization] at index $n-1$ to the coefficient unit
identifies $P$ with $[R\xrightarrow{\pi^n}R]$ in degrees $[-1,0]$, including its quotient
augmentation; hence $P$ is perfect. Write $P^\vee=R\mathcal Hom_R(P,R)$. Perfect duality
[lem-sfb-ringed-site-perfect-duality], followed by the currying and tensor symmetry of
[lem-weil-pbc-ringed-internal-hom-exact-restriction,
lem-sf-ringed-derived-closed-symmetric-monoidal], gives
$$P\otimes_R^LR\mathcal Hom_R(K,L)\simeq R\mathcal Hom_R(P^\vee,R\mathcal Hom_R(K,L))\simeq
R\mathcal Hom_R(K,R\mathcal Hom_R(P^\vee,L))\simeq R\mathcal Hom_R(K,P\otimes_R^LL).$$
Here perfect biduality identifies $(P^\vee)^\vee$ with $P$. By [lem-sfb-dc-hom-scalar-adjunction],
the last object is the restriction of $R\mathcal Hom_S(S\otimes_R^LK,S\otimes_R^LL)$. Every arrow
above is induced by tensor evaluation and the specified quotient unit; consequently their
composite is the restriction of the canonical balanced scalar-Hom comparison. Restriction is
conservative by the same adjunction node, proving that actual comparison invertible in $D(S)$. No
site-perfectness of $K$ is used.

5. The three scalar-extension functors preserve bounded constructibility by
[lem-sfb-extend-scalars-bounded-constructible], [lem-sfb-extend-subfield-constructible] and
[lem-sfb-extend-to-qlbar-constructible], respectively; Step 1 identifies their predicates and
ambient operations with the coefficient categories fixed in the statement. The equivalence
[def-sfb-rationalization-equivalence], whose composite with localization is the actual
$E_X\otimes^L_{O_X}-$, is essentially surjective. Since localization has the same objects as the
integral category, every object of $C_E$ therefore has an integral model $K_O\in C_O$. For
$\Omega$, [lem-sfb-constructible-cocone-obj] gives a finite field $E$ and $K_E\in C_E$ whose
actual scalar extension is the given object. This establishes object descent for the full
categories; it does not replace their ambient Hom groups by a smaller category of chosen models.

6. For $O\to E$, Step 1 makes $K$ bounded constructible in the general ring-object sense, and
boundedness makes $L$ bounded below. The scheme $X$ is Noetherian. These are exactly the
hypotheses of [lem-sfb-integral-general-lfp-hom-inversion]. Its evaluation-transpose isomorphism
$$E_X\otimes^L_{O_X}R\mathcal Hom_{O_X}(K,L)\xrightarrow{\sim}R\mathcal
Hom_{E_X}(E_X\otimes^L_{O_X}K,E_X\otimes^L_{O_X}L)$$
is the required map in the ordinary uncompleted category. Inverting $\ell$ is equivalent to
inverting $\pi$, because $\ell=u\pi^e$ for a unit $u$. The cited node supplies an internal-sheaf
comparison, not merely a comparison on global derived Hom.

7. For finite $E\subseteq F$, [det-prop-sfb-cartesian-coefficients-finite-free] identifies
$P=\operatorname{Res}_{E_X}F_X$ with $E_X^{[F:E]}$. Thus $P$ is perfect. Apply perfect duality
[lem-sfb-ringed-site-perfect-duality] and currying/symmetry
[lem-weil-pbc-ringed-internal-hom-exact-restriction,
lem-sf-ringed-derived-closed-symmetric-monoidal] to obtain exactly the three isomorphisms of Step
4, now with $R=E_X$ and this $P$. Change of rings [lem-sfb-dc-hom-scalar-adjunction] identifies
the final $R\mathcal Hom_R(K,P\otimes_R^LL)$ with the restricted target internal Hom. Hence the
finite-field scalar comparison is an isomorphism. Its normalization is explicit: under any basis
$(b_i)$ the restricted comparison is the direct-sum map sending the $i$th copy of $h$ to $k\mapsto
b_i\otimes h(k)$. This is the transpose of scalar-extended evaluation, so it is independent of the
basis. Conservativity of restriction proves the result before restriction as well.

8. For $E\to\Omega$, [lem-sfb-constructible-internal-hom-continuity] applies to $K\in C_E$ on the
Noetherian space $X$. It gives precisely the internal-sheaf filtered-colimit continuity hypothesis
in [lem-sfb-qlbar-internal-hom-coefficient-comparison]; boundedness of $L$ gives that node's lower
bound. Apply it to conclude that the canonical scalar-Hom comparison is invertible. Concretely the
small filtered set of finite fields $E\subseteq F\subseteq\Omega$ is cofinal, each $F_X$ is finite
free over $E_X$, and its sheaf colimit is $\Omega_X$. The comparison is
$$\Omega_X\otimes^L H_E(K,L)\simeq\varinjlim_F(F_X\otimes
H_E(K,L))\simeq\varinjlim_FH_E(K,F_X\otimes L)\simeq H_E(K,\Omega_X\otimes L),$$
followed by scalar adjunction, exactly as specified in that comparison node. A single
bounded-below representative of $L$ gives a common termwise lower bound after these flat
finite-free extensions. This uses the prescribed finite-subextension-valued coefficient colimit,
with no completion of $\Omega$.

9. For every coefficient map under consideration let $T$ be derived scalar extension,
$\mu:T(A\otimes^LB)\simeq TA\otimes^LTB$, and $c_{A,B}:TH_R(A,B)\to H_S(TA,TB)$. Use the canonical
symmetric monoidal comparisons of [lem-sfb-ringed-derived-monoidal-comparisons]. All maps proved
invertible above are characterized by
$$\operatorname{ev}_S\circ(c_{A,B}\otimes1)=T(\operatorname{ev}_R)\circ\mu^{-1}.$$
In particular they preserve evaluation and the Koszul symmetry, with its actual sign $(-1)^{pq}$.
The tensor-tower normalization of [lem-sfb-scalar-hom-tensor-coherence] gives the hypotheses of
[lem-pur-scalar-hom-comparison-tower], which proves the direct-versus-successive scalar
comparisons equal, including identity coefficients. Naturality is part of the tower node.
Compatibility with first-input shifts is [lem-sfb-ringed-scalar-hom-exact]; for second-input
shifts, transposing either route yields the same shifted scalar-extended evaluation by the scalar
adjunction normalization [lem-sfb-dc-hom-scalar-adjunction]. These assertions apply equally to the
nonflat finite quotient maps; they are assertions about the actual evaluation-transpose maps.

10. Internal composition is the transpose of two successive evaluations, using the closed
adjunction of [lem-sf-ringed-derived-closed-symmetric-monoidal]. To compare scalar extension of
composition with composition of $c_{B,C}$ and $c_{A,B}$, tensor both routes with $TA$ and
evaluate. Step 9 changes the resulting two composites to $T$ of the same successive evaluations
$H_R(B,C)\otimes H_R(A,B)\otimes A\to C$. Their associators agree by
[lem-sfb-ringed-derived-monoidal-comparisons], so injectivity of the adjunction bijection makes
the routes equal. For a scheme isomorphism $g$, pullback and pullback along $g^{-1}$ are inverse
strong monoidal equivalences by the identity and composition clauses of that same node. The closed
adjunction then identifies $g^*H_R(A,B)$ with $H_{g^*R}(g^*A,g^*B)$: test against $g^*Z$ and use
the tensor comparison. Both orders of scheme pullback and coefficient comparison have transpose
$g^*T(\operatorname{ev})$ under the canonical tensor and composition comparisons. The same
adjunction injectivity proves their equality. This proves scheme-isomorphism compatibility on the
full ordinary derived categories.

11. Choose the common pro-étale root cover and compatible primitive roots supplied by
[lem-route-sp-twists-common-cover]. Use precisely the twists constructed in
[sk-def-sp-tate-twist]. In these root frames the quotient and scalar maps send $\zeta_r\otimes a$
to $\zeta_r\otimes a$; the integral transition sends $\zeta_{r+1}\otimes a$ to $\zeta_r\otimes\bar
a$. Thus the canonical scalar map on the integral root line, its finite quotient, and each field
extension is an isomorphism: its cone is acyclic on the root cover, hence acyclic. Here
$(\ell^r)=(\pi^{er})$ makes the two integral filtrations cofinal. Tensor powers and dual rank-one
frames give the isomorphisms for every signed twist. Perfect duality
[lem-sfb-ringed-site-perfect-duality] and currying
[lem-weil-pbc-ringed-internal-hom-exact-restriction] give the canonical formula
$H(K(a),L(b))\simeq H(K,L)\otimes\Lambda_X(b-a)$. To check its compatibility with $c$, transpose
the two global routes using [lem-sf-ringed-derived-closed-symmetric-monoidal]. Both become
scalar-extended evaluation of $K,L$, tensored with the evaluation of the invertible twist and
reordered by the same symmetry. Step 9 makes these global maps equal, so the adjunction bijection
gives the required equality. Local root frames were used only to prove the line maps invertible,
not to infer equality of arbitrary derived morphisms from local equalities.

12. Finally fix $W\in C_\Lambda$ and write $D=H_\Lambda(K,W)\in C_\Lambda$ by Step 2. By
[def-per-ringed-site-bidual-transpose], $b_{W,K}$ is the transpose of $K\otimes
D\xrightarrow{\sigma}D\otimes K\xrightarrow{\mathrm{ev}}W$. The two invertible comparisons
$c_{K,W}$ and $c_{D,W}$ give the explicit target identification
$$TH_\Lambda(D,W)\xrightarrow{c_{D,W}}H_{\Lambda'}(TD,TW)
\xrightarrow{H_{\Lambda'}(c_{K,W}^{-1},1)}H_{\Lambda'}(H_{\Lambda'}(TK,TW),TW).$$
Compose it with $T(b_{W,K})$. Its transpose is, by Step 9 and symmetry, $TK\otimes
H_{\Lambda'}(TK,TW)\xrightarrow{\sigma}\,H_{\Lambda'}(TK,TW)\otimes
TK\xrightarrow{\mathrm{ev}}TW$. This is exactly the defining transpose of $b_{TW,TK}$, so the maps
coincide by the closed adjunction [lem-sf-ringed-derived-closed-symmetric-monoidal]. In the
finite-reduction case the internal Hom target also stays bounded constructible, because Step 4
identifies it with a reduction of $D$ and Step 3 applies. This argument compares the actual bidual
map; it makes no assertion that $b_{W,K}$ is invertible.
-/
theorem constructible_coefficient_hom_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [PerfectField k]
    (hinv : IsUnit (ℓ : k)) (Z : Over (Spec (.of k))) [Smooth Z.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (d : ℕ) (hd : d = 0 ∨ d = 1) (hdim : Z.left.IsPureDimension d) :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      HomClosed Z.left (integral.{u} ℓ E) ∧
      IntegralAssertions Z.left ℓ E ∧
      (∀ n : ℕ, CoherentScalarAssertions Z.left (reductionMap.{u} ℓ E n)) ∧
      CoherentScalarAssertions Z.left (integralToField.{u} ℓ E) ∧
      HomClosed Z.left (Profinite.continuousMapRingObj.{u} E.val) ∧
      (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
        CoherentScalarAssertions Z.left (Profinite.padicSubfieldRingObjMap.{u} ℓ h)) ∧
      CoherentScalarAssertions Z.left (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E) ∧
      (∀ K : D Z.left (Profinite.continuousMapRingObj.{u} E.val),
        bc Z.left (Profinite.continuousMapRingObj E.val) K →
          ∃ L : D Z.left (integral.{u} ℓ E), bc Z.left (integral ℓ E) L ∧
            Nonempty ((scalar Z.left (integralToField ℓ E)).obj L ≅ K)) ∧
      TateAssertions Z.left (integral.{u} ℓ E) (integralLine Z.left ℓ E) ∧
      TateAssertions Z.left (Profinite.continuousMapRingObj.{u} E.val)
        (spRationalTwist Z.left ℓ E)) ∧
    HomClosed Z.left (Profinite.padicAlgClRingObj.{u} ℓ) ∧
    (∀ K : D Z.left (Profinite.padicAlgClRingObj.{u} ℓ),
      bc Z.left (Profinite.padicAlgClRingObj ℓ) K →
        ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
          (L : D Z.left (Profinite.continuousMapRingObj.{u} E.val)),
          bc Z.left (Profinite.continuousMapRingObj E.val) L ∧
          Nonempty ((scalar Z.left
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)).obj L ≅ K)) ∧
    TateAssertions Z.left (Profinite.padicAlgClRingObj.{u} ℓ) (spQbarTwist Z.left ℓ) := by
  sorry

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
