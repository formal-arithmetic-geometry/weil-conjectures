/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorIntegrationSiteComparison
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
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
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
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
public import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantCounit
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
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
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonModelRealizationSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonContinuity
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonRepresentableContinuity
public import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
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
public import WeilConjectures.CategoryTheory.SiteSesCechH1Surjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
public import Mathlib.AlgebraicGeometry.AffineScheme
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
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.CoefficientTorFlatModelSupplement
public import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonFlatPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.HomologicalComplex
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
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.ProjectiveSpaceStandardCharts
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactProjectionFormula

/-! # Canonical coordinate maps for affine-line purity

Source: main-20261015, sec-smooth-purity/sk-prop-an,
affine-line purity comparison, order 2318 (blueprint: def-pur-affine-line-purity-coordinate-maps).

The exact comparison unit, tensor trace composite, actual open-counit trace
restriction, and canonical inverse-image/tensor realization comparisons. No
map of the required type is chosen arbitrarily.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineLinePurity

open VectorIntegrationSite

section Unit
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]

/-- Canonical coefficient-unit comparison. Source: exact monoidal comparison
(blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def coefficientUnitIso (T : Scheme.{u}) :
    (comparisonUpperStar B T).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ (Sheaf T.smallEtaleTopology B))) ≅
        𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T) B)) :=
  ((comparisonUpperStar B T).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (comparisonUpperStar B T)).symm ≪≫
    DerivedCategory.singleFunctorObjUnitIso _

/-- The monoidal right unitor with the compared constant coefficient unit.
Source: derived tensor unit (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def coefficientRightUnit (T : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) B)) :
    ((derivedTensor B T).obj K).obj
      ((comparisonUpperStar B T).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ (Sheaf T.smallEtaleTopology B)))) ≅ K :=
  ((derivedTensor B T).obj K).mapIso (coefficientUnitIso B T) ≪≫
    (CategoryTheory.MonoidalCategory.rightUnitor K)

end Unit

/-- Restriction of a prescribed projective trace by the actual open counit.
This helper is instantiated below with the normalized projective-line trace.
Source: affine-line integration display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def restrictTrace (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (W : Etale.DerivedCategoryModule A (ProjectiveLine T))
    (t : (lowerStar (ModuleCat.{u + 1} A)
      (ProjectiveLine T ↘ T)).rightDerivedFunctor.obj
        ((comparison A (ProjectiveLine T)).obj W) ⟶ unit A T) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification T)).obj
        ((comparison A (AffineSpace PUnit.{u + 1} T)).obj
          ((Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T)).obj W)) ⟶
      unit A T :=
  (lineLeft A T).map ((pullback A (ProjectiveLine.affineChart T)).app W).hom ≫
    (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine T ↘ T)).rightDerivedFunctor.map
      ((openAdjunction A (ProjectiveLine.affineChart T)).counit.app
        ((comparison A (ProjectiveLine T)).obj W)) ≫ t

/-- Compare the canonical shifted ordinary Tate pullback, before coefficient specialization.
Source: canonical Tate inverse image (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def comparedLinePullback (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Z : Scheme.{u}} (f : X ⟶ Z) (hZ : IsUnit (N : Γ(Z, ⊤))) :
    (comparison A X).obj ((Etale.ordinaryFinitePullback A f).obj
      ((Etale.ordinaryFiniteLine A N hA Z)⟦(2 : ℤ)⟧)) ≅
    (comparison A X).obj ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) :=
  (comparison A X).mapIso (Etale.ordinaryFiniteShiftedLinePullback A N hA
    (Etale.projectiveLineTraceTransport N hN A hA) f hZ)

/-- The ordinary tensor-source object, cached before scheme specialization.
Source: ordinary source display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def ordinarySourceObject (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (f : X ⟶ Z) (W : Etale.DerivedCategoryModule A X)
    (K : Etale.DerivedCategoryModule A Z) : Etale.DerivedCategoryModule A X :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((Etale.ordinaryFinitePullback A f).obj K)).obj W

/-- The literal tensor source of the compact-support projection.
Source: Pi_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def projectionSourceObject (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (f : X ⟶ Z)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj F

/-- The actual pro-etale tensor-source object, with compared coefficient.
Source: twisted source display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def proSourceObject (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (f : X ⟶ Z) (W : Etale.DerivedCategoryModule A X)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  projectionSourceObject A f ((comparison A X).obj W) K

/-- Canonical pullback/tensor comparison followed by an arbitrary realization isomorphism.
Source: the displayed ordinary source identification
(blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def realizedTensorComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (f : X ⟶ Z)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (Ke : Etale.DerivedCategoryModule A Z) (W : Etale.DerivedCategoryModule A X)
    (eK : (comparison A Z).obj Ke ≅ K) :
    (comparison A X).obj (ordinarySourceObject A f W Ke) ≅ proSourceObject A f W K := by
  unfold ordinarySourceObject proSourceObject projectionSourceObject
  exact tensorPullbackComparison A f Ke W ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.mapIso eK)).app _

/-- The coefficient right unitor with the literal compared ordinary coefficient unit.
Source: a_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def moduleRightUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj (unit A T) ≅ K :=
  coefficientRightUnit (ModuleCat.{u + 1} A) T K

/-- The literal coefficient-first tensor target of inverse projection.
Source: Pi_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def projectionTargetObject (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :=
  ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).obj
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj F)

/-- Invertibility of the specified canonical coefficient-first projection map.
This is exactly IsIso of the symmetry-adjusted projection transformation.
Source: Pi_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def ProjectionInvertible (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) : Prop :=
  IsIso (projection (ModuleCat.{u + 1} A) c F K)

/-- The inverse of the actual symmetry-adjusted canonical compact-support projection.
Source: Pi_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def inverseProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (h : ProjectionInvertible A c F K) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (projectionSourceObject A f F K) ≅ projectionTargetObject A c F K := by
  unfold projectionSourceObject projectionTargetObject
  unfold ProjectionInvertible at h
  letI := h
  exact (asIso (projection (ModuleCat.{u + 1} A) c F K)).symm

/-- Inverse canonical projection, tensor integration and the literal coefficient unitor.
Source: a_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def projectionTensorTrace (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (t : (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).obj F ⟶ unit A Z)
    (h : ProjectionInvertible A c F K) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (projectionSourceObject A f F K) ⟶ K := by
  let e := inverseProjection A c F K h
  unfold projectionTargetObject at e
  exact e.hom ≫ ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map t ≫
    (moduleRightUnit A Z K).hom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The ordinary Ring structure is the one induced by the existing CommRing structure.
This cache aligns specialized ModuleCat coefficients with the generic canonical maps.
Source: coefficient convention (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
instance (priority := 2000) coefficientRing : Ring (Scheme.finiteTateCoefficient l E n) :=
  (inferInstance : CommRing (Scheme.finiteTateCoefficient l E n)).toRing

/-- Finiteness of the existing positive-level quotient coefficient ring.
Source: finite purity conventions (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
instance coefficientFinite : Finite (Scheme.finiteTateCoefficient l E n) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos _)
  exact inferInstanceAs (Finite (ULift.{u + 1}
    (Padic.coefficientExtensionRing l E (n + 1))))

variable (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)

/-- The canonical finite-Tate comparison for an arbitrary inverse image, including shift.
Its geometric specialization below is the chosen affine chart.
Source: Tate pullback and tau (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def twistPullbackComparison {X Z : Scheme.{u}} (f : X ⟶ Z)
    (hZ : IsUnit (l : Γ(Z, ⊤))) (hX : IsUnit (l : Γ(X, ⊤))) :
    (comparison (Scheme.finiteTateCoefficient l E n) X).obj
      ((Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n) f).obj
        ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA Z)⟦(2 : ℤ)⟧)) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteTateProSheaf l E n X 1))⟦(2 : ℤ)⟧ :=
  comparedLinePullback (Scheme.finiteTateCoefficient l E n)
    (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA f
      (by simpa only [Nat.cast_pow] using hZ.pow (r + 1)) ≪≫
    twistDerived l E n X hX r hA 1 2

end AlgebraicGeometry.ProEtale.AffineLinePurity
