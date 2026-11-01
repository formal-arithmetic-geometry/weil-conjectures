/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteEncoding.IntegralFiniteEncoding
public import WeilConjectures.AlgebraicGeometry.IntegralSmallPerfect.IntegralSmallPerfectTower
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalarRealization
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
public import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.RightDerivedExactComposite
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import WeilConjectures.ProperBaseChange.ConstantCompletionCore
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionFinitePullSupplement
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
public import WeilConjectures.ProperBaseChange.GeometricModuleConstruction
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedAdjunctionCompatibility
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.CoefficientTorFlatModelSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeResidueIdeal
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.Algebra.Homology.AcyclicKFlatTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Module.Torsion.Basic
public import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
public import Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import WeilConjectures.SmoothPurity.CoefficientLocallyConstantCounit
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.ProEtaleCoefficients.CoefficientComparisonConstantChartCounit
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonModelRealizationSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.RingTheory.ProEtale.Etale
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.ProEtaleCoefficients.CoefficientComparisonAffineCech
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechExact
public import WeilConjectures.CategoryTheory.SiteSesCechH1Surjective
public import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.Topology.ConstructibleIsRetrocompact
public import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.ProperBaseChange.RingedToposKFlatPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
public import WeilConjectures.ProperBaseChange.GeometricModuleTransport
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.Algebra.Homology.SmoothPurity.ConstantLocalModuleHomSupplement
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleUnitSupplement
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.CategoryTheory.Sites.ConstantForget
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalModuleIsoSupplement
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.RingTheory.Finiteness.Cardinality
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRestrictedTensorFiniteLocalConstancySupplement
public import WeilConjectures.ProperBaseChange.NilpotentReductionStep
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.SixFunctors.ConstantScalarAlgebraicPullback
public import WeilConjectures.ProperBaseChange.FlatAlgebraicInverseImageOfUniverses
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.SixFunctors.ConstantInverseImageScalarNormalization
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.StdBasis
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.AlgebraicGeometry.ProEtale.WContractibleDisjointCover
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import WeilConjectures.AlgebraicGeometry.Picard.RingedDerivedDisjointIso
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.OfFlat
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSectionGermIsoSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientConnectedStalkConstant
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteConstantEncoding
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteSliceEncodingEquivalence
public import WeilConjectures.WeilObject.Sheaf.Stalk

/-! # Finite constant realization in the normalized coefficient presentation

Source: Stacks Tags 03CY and 093J; integral local structure, proof step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

@[irreducible] private def finiteScalarOrdinaryPullbackComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ (n : ℕ) (X : Scheme.{u}) (W : X.ProEt),
      integralFiniteScalarFunctor l E X n ⋙
          CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) W.hom ≅
        integralFiniteScalarFunctor l E W.left n := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  intro n X W
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let U := ModuleCat.uliftFunctor.{u + 1, u} A
  let B := FiniteConstantModel.scalarModules A
  let C := (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
    (AddCommGrpCat.of (ULift.{u + 1} A))
  let V := Mod.extendScalars (FiniteConstantModel.scalarToContinuous A)
  let P := CondensedRing.upperStarFromPointMod (Profinite.continuousCoefficientRingObj A) X
  let Q := CondensedRing.upperStarFromPointMod (Profinite.continuousCoefficientRingObj A) W.left
  let H := CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) W.hom
  have e : P ⋙ H ≅ Q :=
    CondensedRing.upperStarFromPointModComp (Profinite.continuousCoefficientRingObj A) W.hom
  have m : (B ⋙ C ⋙ V ⋙ P) ⋙ H ≅ B ⋙ C ⋙ V ⋙ Q :=
    Functor.associator B (C ⋙ V ⋙ P) H ≪≫ Functor.isoWhiskerLeft B
      (Functor.associator C (V ⋙ P) H ≪≫ Functor.isoWhiskerLeft C
        (Functor.associator V P H ≪≫ Functor.isoWhiskerLeft V e))
  exact Functor.associator U (B ⋙ C ⋙ V ⋙ P) H ≪≫ Functor.isoWhiskerLeft U m

@[irreducible] private def finiteScalarPullbackComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ (n : ℕ) (X : Scheme.{u}) (W : X.ProEt),
      integralFiniteScalarRealization l E X n ⋙
          (CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1))
            W.hom).mapDerivedCategory ≅
        integralFiniteScalarRealization l E W.left n := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  intro n X W
  letI := comp_preservesFiniteLimits (integralFiniteScalarFunctor l E X n)
    (CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) W.hom)
  letI := comp_preservesFiniteColimits (integralFiniteScalarFunctor l E X n)
    (CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) W.hom)
  exact (Functor.mapDerivedCategoryCompIso (integralFiniteScalarFunctor l E X n)
    (CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) W.hom)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (finiteScalarOrdinaryPullbackComparison l E n X W)

/-- A specified constant model on the coefficient-sized slice gives the actual internal
scalar model on the corresponding scheme. No cohomological or perfectness condition is
needed for this comparison of exact functors.
Source: Stacks Tags 03CY and 093J; blueprint integral local structure, proof step 2
(blueprint: lem-pe-integral-finite-constant-comparison).

Proof: first compare the ordinary functors. The section-action encoding of a scalar
model has the original module as underlying constant sections. Normalization of the
coefficient ring isomorphism makes the actions identical on constant scalar sections.
Local surjectivity of sheafification extends this identity to all scalar sections.
The AsSmall sheaf equivalence and inverse constant-scalar restriction therefore carry
the internal scalar model to the recorded constant module functor. Universe lift and
restriction along the lifted-ring equivalence identify the two scalar presentations.
For scheme restriction, identify the composite direct images on sections and their
constant scalar actions; uniqueness of left adjoints gives the inverse-image comparison.
The AsSmall equivalence identifies its localized site with the slice over W, including
the canonical equivalence maps. These natural isomorphisms are between exact additive
functors, so termwise extension descends through quasi-isomorphisms. Apply the resulting
derived square to the given scalar isomorphism and local constant marking. The normalized
encoding is an equivalence and reflects isomorphisms; undo it to obtain the asserted
internal isomorphism. The argument is valid for arbitrary unbounded complexes and for
empty W and zero coefficients. -/
theorem integralFiniteConstant_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ (n : ℕ) (X : Scheme.{u}) (W : X.ProEt)
      (e : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) X)
      (L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (AdicCompletion.finiteRing l E X n)))
      (M : DerivedCategory (ModuleCat.{u} (Padic.coefficientExtensionRing l E (n + 1))))
      (S : DerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))),
      Nonempty
        ((ModuleCat.uliftFunctor.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj M ≅
          (ModuleCat.restrictScalars.{u + 1}
            (ULift.ringEquiv : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) ≃+*
              Padic.coefficientExtensionRing l E (n + 1)).symm.toRingHom).mapDerivedCategory.obj
              S) →
      Nonempty
        ((Scheme.coefficientSliceConstant.{u, u} X
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
            (AsSmall.up.obj W)).obj S ≅
          (Scheme.adicResidueRestriction
            (ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
            (AsSmall.up.obj W)).obj
              ((IntegralFiniteEncoding.finiteEncodingDerived
                (Padic.coefficientExtensionRing l E (n + 1)) X e).obj L)) →
      Nonempty
        ((integralFiniteScalarRealization l E W.left n).obj M ≅
          (CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1))
            W.hom).mapDerivedCategory.obj L) := by sorry

end AlgebraicGeometry.ProEtale
