/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityCoordinateMaps
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
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-! # The twisted affine-line source and its etale origin

Source: main-20261015, sec-smooth-purity/sk-prop-an,
affine-line purity comparison, order 2318 (blueprint: def-pur-affine-line-purity-source).

The actual compared Tate coefficient, its inverse-limit identification, the
literal twisted inverse image, and its explicit bounded-below ordinary origin.
All comparison isomorphisms are compositions of the recorded canonical maps.
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

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ) (Y : Scheme.{u})

variable (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : (Scheme.finiteTateCoefficient l E n)) = 0)

/-- The shifted ordinary Tate coefficient restricted to the standard affine chart.
The canonical Tate pullback identifies it with B_X[2]. Source: main-20261015,
affine-line purity comparison (blueprint: def-pur-affine-line-purity-source). -/
@[irreducible]
def etaleCoefficient :
    Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n)
      (AffineSpace PUnit.{u + 1} Y) :=
  (Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n)
    (ProjectiveLine.affineChart Y)).obj
    (linePlus l E n r hA (ProjectiveLine Y)).obj

/-- A_X(1)[2] in the canonical comparison coordinates fixed by tau and Tate pullback.
Source: main-20261015, affine-line purity comparison
(blueprint: def-pur-affine-line-purity-source). -/
abbrev coefficient : DerivedCategory
    (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit.{u + 1} Y))
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))) :=
  (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).obj
    (etaleCoefficient l E n Y r hA)

/-- Defining comparison coordinate equality, retained for inexpensive transport.
Source: the displayed coefficient (blueprint: def-pur-affine-line-purity-source).
Proof: unfold coefficient; the two objects are identical by reflexivity. -/
theorem coefficient_comparison_eq : coefficient l E n Y r hA =
    (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).obj
      (etaleCoefficient l E n Y r hA) := by
  rfl

/-- The defining ordinary shifted-line coordinate equality.
Source: the displayed coefficient (blueprint: def-pur-affine-line-purity-source).
Proof: unfold etaleCoefficient and linePlus; the underlying object is identical. -/
theorem etaleCoefficient_eq : etaleCoefficient l E n Y r hA =
    (Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n)
      (ProjectiveLine.affineChart Y)).obj
      ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA (ProjectiveLine Y))⟦(2 : ℤ)⟧) := by
  unfold etaleCoefficient
  rfl

/-- Identification with the specified inverse-limit pro-etale twist, not a new Tate line.
The ordinary pullback is fixed on roots and the final map is tau shifted by two.
Source: main-20261015, Tate comparison paragraph
(blueprint: def-pur-affine-line-purity-source). -/
@[irreducible]
def coefficientTwistIso
    (hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)))
    (hX : IsUnit (l : Γ(AffineSpace PUnit.{u + 1} Y, ⊤))) :
    coefficient l E n Y r hA ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteTateProSheaf l E n
          (AffineSpace PUnit.{u + 1} Y) 1))⟦(2 : ℤ)⟧ :=
  eqToIso (coefficient_comparison_eq l E n Y r hA) ≪≫
    (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).mapIso
      (eqToIso (etaleCoefficient_eq l E n Y r hA)) ≪≫
    twistPullbackComparison l E n r hA (ProjectiveLine.affineChart Y) hP hX

/-- The literal pro-etale twisted inverse image M_K = Lp^*K tensor A_X(1)[2].
Source: main-20261015, transpose display
(blueprint: def-pur-affine-line-purity-source). -/
abbrev source (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit.{u + 1} Y))
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))) :=
  projectionSourceObject (Scheme.finiteTateCoefficient l E n)
    (AffineSpace PUnit.{u + 1} Y ↘ Y) (coefficient l E n Y r hA) K

/-- The explicit ordinary representative of the twisted source.
Source: main-20261015, etale-origin witness
(blueprint: def-pur-affine-line-purity-source). -/
@[irreducible]
def etaleSource (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y) :
    Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n)
      (AffineSpace PUnit.{u + 1} Y) :=
  ordinarySourceObject (Scheme.finiteTateCoefficient l E n)
    (AffineSpace PUnit.{u + 1} Y ↘ Y) (etaleCoefficient l E n Y r hA) K

/-- The literal tensor expression defining the pro-etale source.
Source: M_K display (blueprint: def-pur-affine-line-purity-source).
Proof: unfold source, projectionSourceObject and coefficient; both sides are the same
derived tensor object. -/
theorem source_eq
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    source l E n Y r hA K =
    ((derivedTensor (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (AffineSpace PUnit.{u + 1} Y)).obj
      ((upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (AffineSpace PUnit.{u + 1} Y ↘ Y)).leftDerivedFunctor.obj K)).obj
      (coefficient l E n Y r hA) := by
  unfold source projectionSourceObject
  rfl

/-- The literal tensor expression defining the ordinary source.
Source: ordinary source display (blueprint: def-pur-affine-line-purity-source).
Proof: unfold etaleSource; both sides are the same cached derived tensor object. -/
theorem etaleSource_eq
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y) :
    etaleSource l E n Y r hA Ke =
    ordinarySourceObject (Scheme.finiteTateCoefficient l E n)
      (AffineSpace PUnit.{u + 1} Y ↘ Y) (etaleCoefficient l E n Y r hA) Ke := by
  unfold etaleSource
  rfl

/-- The defining pro-etale coordinate, using the cached literal tensor template.
Source: M_K display (blueprint: def-pur-affine-line-purity-source).
Proof: unfold source, proSourceObject and coefficient; both sides are identical
by reflexivity. -/
theorem source_coordinate_eq
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    source l E n Y r hA K =
    proSourceObject (Scheme.finiteTateCoefficient l E n)
      (AffineSpace PUnit.{u + 1} Y ↘ Y) (etaleCoefficient l E n Y r hA) K := by
  unfold source proSourceObject
  rfl

/-- Canonical tensor/pullback comparison, followed by the chosen realization of K.
Source: main-20261015, explicit witness display
(blueprint: def-pur-affine-line-purity-source). -/
@[irreducible]
def sourceComparison
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :
    (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).obj
      (etaleSource l E n Y r hA Ke) ≅ source l E n Y r hA K :=
  (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).mapIso
      (eqToIso (etaleSource_eq l E n Y r hA Ke)) ≪≫
    realizedTensorComparison (Scheme.finiteTateCoefficient l E n)
      (AffineSpace PUnit.{u + 1} Y ↘ Y) K Ke (etaleCoefficient l E n Y r hA) eK ≪≫
    (eqToIso (source_coordinate_eq l E n Y r hA K)).symm

/-- The representative displayed in the node is bounded below.
Source: main-20261015, bounded etale-origin paragraph
(blueprint: def-pur-affine-line-purity-source).
Proof: Ke is bounded constructible of finite Tor amplitude. Exact p_e^* preserves
its bounds. Tensoring a finite-Tor-amplitude complex with the degree-zero
ordinary Tate sheaf has a finite lower bound, shifted by -2. On the unit-prime
domain of the node the Tate sheaf is furthermore locally free of rank one. -/
theorem etaleSource_plus (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke) :
    DerivedCategory.TStructure.t.plus (etaleSource l E n Y r hA Ke) := by
  let A := Scheme.finiteTateCoefficient l E n
  let X := AffineSpace PUnit.{u + 1} Y
  have hp := Etale.constructibleFiniteTor_leftDerivedUpperStar
    (ModuleCat.{u + 1} A) (X ↘ Y) hKe
  obtain ⟨a, b, ht⟩ := hp.2
  have hc : (etaleCoefficient l E n Y r hA).IsGE (-2) := by
    rw [etaleCoefficient_eq]
    have hs := DerivedCategory.TStructure.t.isGE_shift
      (Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine Y)) 0 2 (-2)
    have hm := (Etale.upperStar (ModuleCat.{u + 1} A)
      (ProjectiveLine.affineChart Y)).isGE_mapDerivedCategory_obj
        ((Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine Y))⟦(2 : ℤ)⟧) (-2)
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart Y)).app _).symm (-2)
  unfold etaleSource ordinarySourceObject
  exact ⟨a + (-2), DerivedCategory.isGE_tensor_of_torAmplitudeIn ht _ (-2)⟩

/-- The realized source has the same lower bound.
Source: main-20261015, bounded etale-origin paragraph
(blueprint: def-pur-affine-line-purity-source).
Proof: exact comparison preserves the lower bound of etaleSource_plus.
Transfer it along sourceComparison. This uses no exceptional adjunction. -/
theorem source_plus
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :
    DerivedCategory.TStructure.t.plus (source l E n Y r hA K) := by
  obtain ⟨a, ha⟩ := etaleSource_plus l E n Y r hA Ke hKe
  have hc := (comparisonUpperStar (ModuleCat.{u + 1}
    (Scheme.finiteTateCoefficient l E n)) (AffineSpace PUnit.{u + 1} Y)).isGE_mapDerivedCategory_obj
      (etaleSource l E n Y r hA Ke) a
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    (sourceComparison l E n Y r hA K Ke eK) ⟨a, hc⟩

/-- The retained pair consisting of the explicit ordinary source and canonical iso.
Source: main-20261015, bounded etale-origin paragraph
(blueprint: def-pur-affine-line-purity-source). -/
@[irreducible]
def sourceWitness
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :
    Scheme.FixedEtaleOriginWitness (AffineSpace PUnit.{u + 1} Y)
      (Scheme.finiteTateCoefficient l E n)
      ⟨source l E n Y r hA K, source_plus l E n Y r hA K Ke hKe eK⟩ where
  complex := ⟨etaleSource l E n Y r hA Ke, etaleSource_plus l E n Y r hA Ke hKe⟩
  iso := sourceComparison l E n Y r hA K Ke eK

end AlgebraicGeometry.ProEtale.AffineLinePurity
