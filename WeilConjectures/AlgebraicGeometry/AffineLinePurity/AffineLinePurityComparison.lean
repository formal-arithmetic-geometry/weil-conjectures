/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePuritySource
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

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-! # The affine-line purity comparison

Source: main-20261015, sec-smooth-purity/sk-prop-an,
def-pur-affine-line-purity-comparison, order 2318
(blueprint: def-pur-affine-line-purity-comparison).

## Main definitions

* `integration`: restriction of the projective trace by the actual open counit.
* `projectionIso` and `augmentation`: Pi_K and a_K with the specified tensor order.
* `sourceWitness`: the retained canonical ordinary origin of M_K.
* `affineLinePurityComparison`: the specified restricted Hom transpose of a_K.

The trace is restricted by the actual extension-by-zero counit. Inverse canonical
projection and the coefficient unitor define a_K. Its specified bounded etale-origin
transpose defines gamma. The chosen representative supplies only applicability data.
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
variable (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)

/-- Restrict the existing projective trace by the actual open-extension counit.
The initial comparison identifies C_X j_e^* B_P[2] with j_p^* C_P B_P[2].
Source: main-20261015, integration display
(blueprint: def-pur-affine-line-purity-comparison). -/
@[irreducible]
def integration [IsNoetherian Y] (hY : IsUnit (l : Γ(Y, ⊤))) :
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (affineTraceLineCompactification Y)).obj (coefficient l E n Y r hA) ⟶
        unit (Scheme.finiteTateCoefficient l E n) Y :=
  (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (affineTraceLineCompactification Y)).map
      ((eqToIso (coefficient_comparison_eq l E n Y r hA)).hom ≫
        (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).map
          (eqToHom (etaleCoefficient_eq l E n Y r hA))) ≫
    restrictTrace (Scheme.finiteTateCoefficient l E n) Y
      ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA (ProjectiveLine Y))⟦(2 : ℤ)⟧)
      (projectiveTrace l E n Y hY (infinityCartier Y) r hA)

attribute [local irreducible] projectionMapOfCompactification

/-- Insert the two canonical signed symmetries around an invertible projection component.
Source: the coefficient-first projection display
(blueprint: def-pur-affine-line-purity-comparison). -/
private theorem reorderedProjection_isIso
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) B))
    (h : IsIso (((projectionMapOfCompactification B c).app F).app K)) :
    IsIso (projection B c F K) := by
  unfold projection
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h inferInstance)

/-- Exact ordinary inverse image preserves boundedness via its canonical derived comparison.
Source: exact constant-coefficient inverse image
(blueprint: def-pur-affine-line-purity-comparison). -/
private theorem ordinaryPullback_bounded
    (A : Type (u + 1)) [CommRing A] {X Z : Scheme.{u}} (f : X ⟶ Z)
    (W : Etale.DerivedCategoryModule A Z) (hW : DerivedCategory.TStructure.t.bounded W) :
    DerivedCategory.TStructure.t.bounded ((Etale.ordinaryFinitePullback A f).obj W) := by
  exact DerivedCategory.TStructure.t.bounded.prop_of_iso
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app W).symm
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).bounded_mapDerivedCategory_obj hW)

/-- A Tate sheaf in degree zero, shifted by two, is bounded in [-2,-2].
Source: the shifted Tate coefficient in the projection display
(blueprint: def-pur-affine-line-purity-comparison). -/
private theorem shiftedLine_bounded (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) :
    DerivedCategory.TStructure.t.bounded ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) := by
  exact ⟨⟨-2, DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2)⟩,
    ⟨-2, DerivedCategory.TStructure.t.isLE_shift _ 0 2 (-2)⟩⟩

/-- The published projection comparison reduction, on the required ordinary origins.
Source: finite compact projection formula, boundedness and comparison steps
(blueprint: def-pur-affine-line-purity-comparison). -/
private theorem projectionFromOrigin_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (hW : DerivedCategory.TStructure.t.bounded W)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (Ke : Etale.DerivedCategoryModule A Z)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Z Ke)
    (eK : (comparison A Z).obj Ke ≅ K) :
    IsIso (projection (ModuleCat.{u + 1} A) c ((comparison A X).obj W) K) := by
  obtain ⟨a, b, hTor⟩ := hKe.2
  have hM := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) c.i).bounded_mapDerivedCategory_obj hW
  have hML := Etale.plus_derivedTensor_leftDerivedUpperStar c.g hM hTor
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite A c.g
  have hPF := hasProjectionFormulaOfCompactification_of_comparison c
    (Iso.refl ((comparison A X).obj W)) eK hW hML inferInstance
  exact reorderedProjection_isIso (ModuleCat.{u + 1} A) c _ K hPF

-- Retain the public geometric applicability parameters; the generic proof needs fewer.
set_option linter.unusedVariables false in
/-- Invertibility of precisely the symmetry-adjusted canonical projection map.
Source: main-20261015, Pi_K paragraph
(blueprint: def-pur-affine-line-purity-comparison).
Proof: the ordinary Tate sheaf shifted by two is bounded in [-2,-2]. Exact
chart pullback and open extension preserve boundedness. The finite Tor interval
of Ke makes its tensor with that extension bounded below. Apply the finite-ring
proper projection formula and its published pro-etale comparison reduction at
the specified compactification, with eK and the literal coefficient origin.
The two signed tensor symmetries preserve invertibility of this canonical map.
No ambient exceptional adjunction is assumed. -/
theorem projection_isIso
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :
    ProjectionInvertible (Scheme.finiteTateCoefficient l E n)
      (affineTraceLineCompactification Y) (coefficient l E n Y r hA) K := by
  have hW : DerivedCategory.TStructure.t.bounded (etaleCoefficient l E n Y r hA) := by
    unfold etaleCoefficient
    exact ordinaryPullback_bounded (Scheme.finiteTateCoefficient l E n)
      (ProjectiveLine.affineChart Y) _
      (shiftedLine_bounded (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA (ProjectiveLine Y))
  unfold ProjectionInvertible
  exact projectionFromOrigin_isIso (Scheme.finiteTateCoefficient l E n)
    (affineTraceLineCompactification Y) (etaleCoefficient l E n Y r hA) hW K Ke hKe eK

/-- Pi_K is the inverse of PF, with the two specified tensor symmetries.
Source: main-20261015, Pi_K display
(blueprint: def-pur-affine-line-purity-comparison). -/
@[irreducible]
def projectionIso
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :=
  inverseProjection (Scheme.finiteTateCoefficient l E n)
      (affineTraceLineCompactification Y) (coefficient l E n Y r hA) K
      (projection_isIso l E n Y r hA k aY hY K Ke hKe eK)

/-- The literal composite Pi_K, tensor of integration, and the coefficient right unitor.
The representative is used only to prove the projection map invertible.
Source: main-20261015, a_K display
(blueprint: def-pur-affine-line-purity-comparison). -/
@[irreducible]
def augmentation [IsNoetherian Y]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :=
  projectionTensorTrace (Scheme.finiteTateCoefficient l E n)
      (affineTraceLineCompactification Y) (coefficient l E n Y r hA) K
      (integration l E n Y r hA hY)
      (projection_isIso l E n Y r hA k aY hY K Ke hKe eK)

/-- The existing ordinary adjoint at the literal affine-chart compactification.
Source: ordinary exceptional adjunction (blueprint: def-pur-affine-line-purity-comparison). -/
instance ordinaryLeftAdjoint :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (affineTraceLineCompactification Y)).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    (Scheme.finiteTateCoefficient l E n) _

/-- The specified restricted transpose, before specializing the finite purity setting.
The source origin and tensor integration are the explicit constructions above.
Source: gamma display (blueprint: def-pur-affine-line-purity-comparison). -/
@[irreducible]
def comparisonFromOrigin
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K.obj) :
    source l E n Y r hA K.obj ⟶
      (sfFiniteExceptionalAt (Scheme.finiteTateCoefficient l E n)
        (affineTraceLineCompactification Y)).obj K.obj :=
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  specifiedExceptionalHomEquiv (Scheme.finiteTateCoefficient l E n)
    (affineTraceLineCompactification Y)
    ⟨source l E n Y r hA K.obj, source_plus l E n Y r hA K.obj Ke hKe eK⟩
    (sourceWitness l E n Y r hA K.obj Ke hKe eK) K
      (augmentation l E n Y r hA hY k aY K.obj Ke hKe eK)

variable (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})

/-- The existing coefficient quotient at the node's positive exponent.
The Tate API is zero based: positivity gives (P.level - 1) + 1 = P.level.
Source: finite purity conventions (blueprint: def-pur-affine-line-purity-comparison). -/
abbrev Ring := Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)

/-- Canonical reindexing to the coefficient of the purity conventions.
Source: positive coefficient level (blueprint: def-pur-affine-line-purity-comparison). -/
def ringEquiv : Ring P ≃+* P.Coefficient :=
  RingEquiv.cast (R := fun m : ℕ ↦ ULift.{u + 1}
    (Padic.coefficientExtensionRing P.coefficients.l P.extension m))
      (Nat.sub_add_cancel P.level_pos)

variable (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)

/-- The coefficient prime is invertible on the base.
Source: finite purity conventions, ell different from the characteristic
(blueprint: def-pur-affine-line-purity-comparison).
Proof: def-pur-conventions supplies coefficientPrime_isUnit_stalk at every point.
The local criterion isUnit_of_isUnit_germ gives invertibility of the constant
global section ell; natCast is preserved by every germ map. The empty scheme
also satisfies this criterion. -/
theorem primeUnit (aY : Y ⟶ Spec (.of P.field.k)) :
    IsUnit (P.coefficients.l : Γ(Y, ⊤)) := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ
  intro y hy
  simpa only [map_natCast] using P.coefficientPrime_isUnit_stalk Y aY y

/-- The affine-line purity comparison gamma_{p,K}, defined as Phi(a_K).
The input Ke and eK are the chosen ordinary finite-Tor representative of K;
finiteTorComparisonNoetherian ensures that every K in D^b_ctf has such inputs.
No exceptional adjunction on arbitrary pro-etale complexes is used, and no
isomorphy of gamma is asserted.
Source: main-20261015, final affine-line purity comparison display
(blueprint: def-pur-affine-line-purity-comparison). -/
@[irreducible]
def affineLinePurityComparison
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) :
    source P.coefficients.l P.extension (P.level - 1) Y r hA K.obj ⟶
      (sfFiniteExceptionalAt (Ring P) (affineTraceLineCompactification Y)).obj K.obj :=
  comparisonFromOrigin P.coefficients.l P.extension (P.level - 1) Y r hA
    P.field.k aY (primeUnit P Y aY) K Ke hKe eK

end AlgebraicGeometry.ProEtale.AffineLinePurity
