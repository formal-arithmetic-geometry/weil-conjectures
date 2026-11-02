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
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteLevels
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.NilpotentCoefficientTensorAcyclic
public import WeilConjectures.AlgebraicGeometry.AdicExactComparison
public import WeilConjectures.AlgebraicGeometry.AdicFiniteEtaleOrigins
public import WeilConjectures.AlgebraicGeometry.AdicFiniteEtaleTransitions
public import WeilConjectures.AlgebraicGeometry.AdicScalarExtensionBound
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedClassicalDescent
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFiniteReflection
public import WeilConjectures.AlgebraicGeometry.CoefficientConnectedStalkConstant
public import WeilConjectures.AlgebraicGeometry.CoefficientConstantTensorLocalModels
public import WeilConjectures.AlgebraicGeometry.CoefficientEtaleStalkScalarExtension
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
public import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived

/-! # Compatible finite etale origins on a lisse stratum

Source: current blueprint, integral local structure, proof step 2; Stacks Tags 099Y and 09AL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The actual constant-coefficient etale derived category at a positive integral level.
Source: Stacks Tag 09AL (blueprint: lem-pe-integral-finite-etale-models). -/
abbrev integralFiniteEtaleModel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) :=
  ConstantCompletion.D (ConstantCompletion.constant
    (Scheme.smallModelComparisonEtaleTopology.{u, u} X)
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))

private def scalar_restriction_coordinates
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type v) [CommRing A] :
    ConstantScalarRestriction.restriction J A ≅ coefficientModelFixedScalars J A := by
  have hu (U : Cᵒᵖ) (r : A) :
      ((constantCommuteCompose J (forget₂ CommRingCat.{v} RingCat.{v})).inv.app
        (CommRingCat.of A)).hom.app U
          ((toSheafify J ((Functor.const _).obj (RingCat.of A))).app U r) =
        (toSheafify J ((Functor.const _).obj (CommRingCat.of A))).app U r := by
    have h := toSheafify_naturality J (Functor.constComp _ (CommRingCat.of A)
      (forget₂ CommRingCat.{v} RingCat.{v})).inv
    change ((toSheafify J ((Functor.const _).obj (RingCat.of A)) ≫
      sheafifyMap J (Functor.constComp _ (CommRingCat.of A)
        (forget₂ CommRingCat.{v} RingCat.{v})).inv ≫
      (sheafifyComposeIso J (forget₂ CommRingCat.{v} RingCat.{v}) _).hom).app U) r = _
    erw [← Category.assoc, ← h, Category.assoc, sheafComposeIso_hom_fac]
    rfl
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun r ↦ ?_))
      (by intro U V f; ext x; rfl))) (by intro M N f; ext U x; rfl)
  ext x
  change ((toSheafify J ((Functor.const _).obj (CommRingCat.of A))).app U r) •
      (show M.val.obj U from x) =
    (((constantCommuteCompose J (forget₂ CommRingCat.{v} RingCat.{v})).inv.app
      (CommRingCat.of A)).hom.app U
        ((toSheafify J ((Functor.const _).obj (RingCat.of A))).app U r)) •
      (show M.val.obj U from x)
  rw [hu]

private theorem small_site_monoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Nonempty (IntegralFiniteEncoding.smallSiteSheafEquivalence X A).functor.Monoidal := by
  let J := Scheme.ProEt.topology X
  let T := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let G : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, u} X := AsSmall.up
  let E := IntegralFiniteEncoding.smallSiteSheafEquivalence X A
  have : G.IsEquivalence := (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).isEquivalence_functor
  have : G.IsContinuous J T := Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} X
  let L := Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{u + 1} A) J T
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    G (ModuleCat.{u + 1} A) J T
  let a' : E.functor ⊣ G.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J T :=
    E.toAdjunction
  exact ⟨Functor.Monoidal.transport (a.leftAdjointUniq a')⟩

private theorem encoding_monoidal (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (X : Scheme.{u})
    (e : FiniteDiscreteOrdinary.Encoding A X) :
    Nonempty (IntegralFiniteEncoding.finiteEncodingFunctor A X e).Monoidal := by
  let B := ULift.{u + 1} A
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let E := IntegralFiniteEncoding.smallFixedScalarsEquivalence X B
  let : (ConstantScalarRestriction.restriction J B).Monoidal :=
    (ConstantScalarRestriction.ordinary J B).braided.toMonoidal
  let : E.functor.Monoidal :=
    Functor.Monoidal.transport (scalar_restriction_coordinates J B)
  let : E.inverse.Monoidal := E.inverseMonoidal
  obtain ⟨mo⟩ := FiniteDiscreteOrdinary.ordinary_monoidal A X e
  let := mo
  obtain ⟨mf⟩ := FiniteDiscreteOrdinary.fixed_monoidal A X e
  let := mf
  obtain ⟨ms⟩ := small_site_monoidal X B
  let := ms
  unfold IntegralFiniteEncoding.finiteEncodingFunctor
  exact ⟨inferInstance⟩

private theorem encoded_local_models
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] (X : Scheme.{u})
    (e : FiniteDiscreteOrdinary.Encoding A X) (M : FiniteDiscreteOrdinary.Internal A X)
    (hM : HasFiniteConstantLocalModel (FiniteDiscreteOrdinary.coefficient A) X M) :
    IsCoefficientModelLocallyConstantFinite
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ULift.{u + 1} A)
      ((coefficientModelFixedScalars _ (ULift.{u + 1} A)).obj
        ((IntegralFiniteEncoding.finiteEncodingFunctor A X e).obj M)) := by
  let B := ULift.{u + 1} A
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let S := IntegralFiniteEncoding.smallSiteSheafEquivalence X B
  let E := IntegralFiniteEncoding.smallFixedScalarsEquivalence X B
  have h := (FiniteDiscreteOrdinary.localCondition_iff A X e M).mp hM
  have hf := (Scheme.finiteLocal_fixedModels X A _).mp h
  have hf' := Scheme.ProFiniteModels.fixedModels_of_iso (Scheme.ProEt.topology X) B
    (FiniteDiscreteOrdinary.fixedIso A X e (e.ordinary.functor.obj M)).symm hf
  have hs := (Scheme.ProFiniteModels.fixedModels_asSmall (Scheme.ProEt.topology X) B _).mp hf'
  exact coefficientProEtale_finite_iso B
    (E.counitIso.app (S.functor.obj ((e.ordinary.functor ⋙ e.fixed.functor).obj M))).symm hs

private theorem finite_lisse_constructible (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) A))
    (hF : IsCoefficientModelLocallyConstantFinite _ A
      ((coefficientModelFixedScalars _ A).obj F)) :
    Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, u} X A F := by
  intro U _
  let S := Scheme.identityStratification U.toScheme
  refine ⟨S, S.isConstructible_stratum, ?_⟩
  intro i V
  let g := S.immersion i ≫ U.ι
  have := model_preserves.{u, u} g
  have h := coefficient_finite_local_systems_pullback
    (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (Scheme.coefficientProEtaleModelTopology.{u, u} (S.domain i))
    (Scheme.coefficientProEtaleModelBaseChange.{u, u} g) A _ hF V
  obtain ⟨T, hT, hm⟩ := h
  refine ⟨T, hT, fun W f hf ↦ ?_⟩
  obtain ⟨M, hM, he⟩ := hm W f hf
  let := hM
  exact ⟨M, Module.finitePresentation_of_finite A M, he⟩

private theorem encoded_tor
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e : FiniteDiscreteOrdinary.Encoding A X)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A X)) (a b : ℤ) (hab : a ≤ b)
    (ht : DerivedCategory.torAmplitudeIn _ a b K) :
    HasCoefficientModelTorAmplitude _
      ((IntegralFiniteEncoding.finiteEncodingDerived A X e).obj K) a b := by
  let R := ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (ULift.{u + 1} A)
  let := moduleMonoidal R
  let := moduleSymmetric R
  let := moduleClosed R
  let := modulePreadditive R
  let := moduleGrothendieck R
  let := moduleFlatResolution R
  let F := IntegralFiniteEncoding.finiteEncodingFunctor A X e
  obtain ⟨m⟩ := encoding_monoidal A X e
  let := m
  let : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  exact (nativeTor_iff R _ a b hab).mp
    (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj F ht)

private theorem finite_lisse_origin
    (Y : Scheme.{u}) [IsNoetherian Y]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (M : Scheme.adicFiniteAmbient.{u, u} Y A) (a b : ℤ)
    (hM : coefficientBoundedConstructibleProEtale.{u, u} Y A M)
    (hTor : Scheme.HasCoefficientProEtaleTorAmplitude.{u, u} Y A M a b)
    (hfinite : ∀ q : ℤ, IsCoefficientModelLocallyConstantFinite
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y) A
      ((coefficientModelFixedScalars _ A).obj ((coefficientModelCohomology _ q).obj M))) :
    ∃ C : ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, u} Y) A),
      (∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
        IsZero ((coefficientModelCohomology _ q).obj C)) ∧
      (∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
        (Scheme.smallModelComparisonEtaleTopology.{u, u} Y) A
        ((coefficientModelCohomology _ q).obj C)) ∧
      HasCoefficientModelTorAmplitude _ C a b ∧
      Nonempty ((Scheme.adicFinitePullback.{u, u} Y A).obj C ≅ M) := by
  obtain ⟨D, ⟨α⟩, ht, E, ⟨β⟩⟩ := finiteTorComparisonNoetherian.{u, u} Y A
  obtain ⟨γ⟩ := Scheme.adicFinitePullback_comparison.{u, u} Y A D α
  let M' : ObjectProperty.FullSubcategory
      (fun K ↦ coefficientBoundedConstructibleProEtale.{u, u} Y A K ∧
        Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u} Y A K) := ⟨M, hM, a, b, hTor⟩
  let C' := E.inverse.obj M'
  let i : D.obj C'.obj ≅ M := (β.app C').symm ≪≫
    (ObjectProperty.ι _).mapIso (E.counitIso.app M')
  have hC := (ht C'.obj C'.property.1 a b hTor.1).mpr
    (Scheme.adicFiniteTor_iso _ i.symm a b hTor)
  let e : (Scheme.adicFinitePullback.{u, u} Y A).obj C'.obj ≅ M := γ.app C'.obj ≪≫ i
  refine ⟨C'.obj, ⟨a, b, Scheme.adicFiniteTor_cohomology_bounds _ _ a b hC⟩, ?_, hC, ⟨e⟩⟩
  obtain ⟨D₀, ⟨α₀⟩, hH, _⟩ := constructibleComparison_derivedFunctor.{u, u} Y A
  obtain ⟨γ₀⟩ := Scheme.adicFinitePullback_comparison.{u, u} Y A D₀ α₀
  intro q
  let iH : (constructibleComparisonPullback.{u, u} Y A).obj
      ((coefficientModelCohomology _ q).obj C'.obj) ≅
      (coefficientModelCohomology _ q).obj M :=
    ((hH q).some.app C'.obj).symm ≪≫
      (coefficientModelCohomology _ q).mapIso ((γ₀.app C'.obj).symm ≪≫ e)
  apply (local_models_iff _ A _).mpr
  apply coefficientComparison_finite_reflect.{u, u} Y A
  exact coefficientProEtale_finite_iso A
    (((comparison_scalars.{u, u} Y A).app ((coefficientModelCohomology _ q).obj C'.obj)).symm ≪≫
      (coefficientModelFixedScalars _ A).mapIso iH).symm (hfinite q)

/-- Finite-level origin data before imposing compatibility of consecutive levels.
Source: Stacks Tags 09AL and 099Y; proof step 2 of the integral local structure argument
(blueprint: lem-pe-integral-finite-etale-level-models).

The proof applies finite-coefficient constructible comparison separately to each reduction.
The coefficient encoding transports the resulting etale origin back to the normalized
finite presentation. The bounded cohomology, lisse finite-type condition, and Tor interval
are transported along the comparison isomorphisms. The construction is independent for
each level, so no transition maps are asserted here. -/
theorem integralFiniteEtale_level_models
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [IsImmersion f]
    (K : DerivedCategory (AdicCompletion.Modules l E X)) (a b : ℤ) (hab : a ≤ b)
    (hlevels : ∀ n : ℕ,
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
        ((AdicCompletion.derivedReduction l E X n).obj K) ∧
      DerivedCategory.torAmplitudeIn _ a b ((AdicCompletion.derivedReduction l E X n).obj K))
    (hlisse : ∀ (n : ℕ) (q : ℤ),
      HasFiniteConstantLocalModel (DerivedNakayama.quotientRing l E (n + 1)) Y
        ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) f).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((AdicCompletion.derivedReduction l E X n).obj K)))) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∃ (e : ∀ n : ℕ, FiniteDiscreteOrdinary.Encoding
          (Padic.coefficientExtensionRing l E (n + 1)) Y)
      (C : ∀ n : ℕ, integralFiniteEtaleModel l E Y n),
      (∀ n : ℕ,
        (∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
          IsZero ((coefficientModelCohomology _ q).obj (C n))) ∧
        (∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
          (Scheme.smallModelComparisonEtaleTopology.{u, u} Y)
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
          ((coefficientModelCohomology _ q).obj (C n))) ∧
        HasCoefficientModelTorAmplitude _ (C n) a b) ∧
      ∀ n : ℕ, Nonempty
        ((IntegralFiniteEncoding.finiteEncodingDerived
          (Padic.coefficientExtensionRing l E (n + 1)) Y (e n)).obj
            ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1))
              f).mapDerivedCategory.obj
                ((AdicCompletion.derivedReduction l E X n).obj K)) ≅
          (Scheme.adicFinitePullback.{u, u} Y
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).obj (C n)) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let e (n : ℕ) : FiniteDiscreteOrdinary.Encoding
      (Padic.coefficientExtensionRing l E (n + 1)) Y := by
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    let : DiscreteTopology A := DerivedNakayama.quotientDiscrete l E (n + 1)
    exact (FiniteDiscreteOrdinary.encoding_exists A Y).some
  have hex (n : ℕ) : ∃ C : integralFiniteEtaleModel l E Y n,
      (∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
        IsZero ((coefficientModelCohomology _ q).obj C)) ∧
      (∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
        (Scheme.smallModelComparisonEtaleTopology.{u, u} Y)
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
        ((coefficientModelCohomology _ q).obj C)) ∧
      HasCoefficientModelTorAmplitude _ C a b ∧ Nonempty
        ((Scheme.adicFinitePullback.{u, u} Y
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).obj C ≅
          (IntegralFiniteEncoding.finiteEncodingDerived
            (Padic.coefficientExtensionRing l E (n + 1)) Y (e n)).obj
            ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1))
              f).mapDerivedCategory.obj
                ((AdicCompletion.derivedReduction l E X n).obj K))) := by
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := ULift.{u + 1} A
    let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    let : DiscreteTopology A := DerivedNakayama.quotientDiscrete l E (n + 1)
    let P := (AdicCompletion.derivedReduction l E X n).obj K
    let U := CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) f
    let L := U.mapDerivedCategory.obj P
    let F := IntegralFiniteEncoding.finiteEncodingFunctor A Y (e n)
    let M := (IntegralFiniteEncoding.finiteEncodingDerived A Y (e n)).obj L
    have htL : DerivedCategory.torAmplitudeIn _ a b L :=
      DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj U (hlevels n).2
    have htM := encoded_tor A Y (e n) L a b hab htL
    have hfM (q : ℤ) : IsCoefficientModelLocallyConstantFinite
        (Scheme.coefficientProEtaleModelTopology.{u, u} Y) B
        ((coefficientModelFixedScalars _ B).obj ((coefficientModelCohomology _ q).obj M)) := by
      let i : F.obj (U.obj ((DerivedCategory.homologyFunctor _ q).obj P)) ≅
          (coefficientModelCohomology _ q).obj M :=
        F.mapIso ((U.mapDerivedCategoryHomologyFunctorIso q).app P) ≪≫
          (F.mapDerivedCategoryHomologyFunctorIso q).app L
      exact coefficientProEtale_finite_iso B ((coefficientModelFixedScalars _ B).mapIso i)
        (encoded_local_models A Y (e n) _ (hlisse n q))
    have hcM : coefficientBoundedConstructibleProEtale.{u, u} Y B M :=
      ⟨fun q ↦ finite_lisse_constructible Y B _ (hfM q), a, b, hab,
        Scheme.adicFiniteTor_cohomology_bounds _ _ a b htM⟩
    exact finite_lisse_origin Y B M a b hcM htM hfM
  choose C hC using hex
  exact ⟨e, C, fun n ↦ ⟨(hC n).1, (hC n).2.1, (hC n).2.2.1⟩,
    fun n ↦ ⟨(hC n).2.2.2.some.symm⟩⟩

private theorem canonical_coefficient_naturality
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (X : Scheme.{u}) (g : AddCommGrpCat.of (ULift.{u + 1} A) ⟶
      AddCommGrpCat.of (ULift.{u + 1} B))
    (φ : FiniteDiscreteOrdinary.coefficient A ⟶ FiniteDiscreteOrdinary.coefficient B)
    (h : (Functor.const Profinite.{u}ᵒᵖ).map g ≫ FiniteDiscreteOrdinary.pointConstants B =
      FiniteDiscreteOrdinary.pointConstants A ≫ φ.hom) :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map g ≫
      FiniteDiscreteOrdinary.canonicalAbelianMap B X =
    FiniteDiscreteOrdinary.canonicalAbelianMap A X ≫ (upperStarFromPoint X).map φ := by
  let adj := sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}
  let α := (adj.homEquiv _ (FiniteDiscreteOrdinary.coefficient A)).symm
    (FiniteDiscreteOrdinary.pointConstants A)
  let β := (adj.homEquiv _ (FiniteDiscreteOrdinary.coefficient B)).symm
    (FiniteDiscreteOrdinary.pointConstants B)
  have hφ : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map g ≫ β =
      α ≫ φ := by
    apply (adj.homEquiv _ _).injective
    change (adj.homEquiv _ _) ((presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      ((Functor.const _).map g) ≫ β) = _
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    simpa only [α, β, Equiv.apply_symm_apply, sheafToPresheaf_map] using h
  change _ ≫ (constantSchemeIso X).hom.app _ ≫ (upperStarFromPoint X).map β =
    ((constantSchemeIso X).hom.app _ ≫ (upperStarFromPoint X).map α) ≫
      (upperStarFromPoint X).map φ
  rw [← Category.assoc, (constantSchemeIso X).hom.naturality g]
  change ((constantSchemeIso X).hom.app _ ≫
    (upperStarFromPoint X).map ((constantSheaf _ _).map g)) ≫
      (upperStarFromPoint X).map β = _
  rw [Category.assoc, ← Functor.map_comp, hφ, Functor.map_comp, Category.assoc]

private theorem encoded_scalar_smul
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (X : Scheme.{u}) (f : A →+* B)
    (φ : condensedRingObj (FiniteDiscreteOrdinary.coefficient A) X ⟶
      condensedRingObj (FiniteDiscreteOrdinary.coefficient B) X) [IsMonHom φ]
    (eA : FiniteDiscreteOrdinary.Encoding A X) (eB : FiniteDiscreteOrdinary.Encoding B X)
    (hn : ∀ (V : X.ProEtᵒᵖ) (a : ULift.{u + 1} A),
      φ.hom.app V
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
            (FiniteDiscreteOrdinary.canonicalAbelianMap A X).hom).app V a) =
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
            (FiniteDiscreteOrdinary.canonicalAbelianMap B X).hom).app V (ULift.up (f a.down))))
    (M : FiniteDiscreteOrdinary.Internal B X) (V : X.ProEtᵒᵖ)
    (a : ULift.{u + 1} A) (m : M.X.obj.obj V) :
    a • (show ((FiniteDiscreteOrdinary.sectionEncoding A X eA.ringIso ⋙
        FiniteDiscreteOrdinary.fixedRestriction A X).obj ((Mod.comap φ).obj M)).obj.obj V
        from m) =
      (ULift.up (f a.down) : ULift.{u + 1} B) •
        (show ((FiniteDiscreteOrdinary.sectionEncoding B X eB.ringIso ⋙
          FiniteDiscreteOrdinary.fixedRestriction B X).obj M).obj.obj V from m) := by
  erw [FiniteDiscreteOrdinary.encoding_smul A X eA,
    FiniteDiscreteOrdinary.encoding_smul B X eB]
  let r := ((toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
      (FiniteDiscreteOrdinary.canonicalAbelianMap A X).hom).app V a)
  change ((Functor.LaxMonoidal.μ
      (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (FiniteDiscreteOrdinary.coefficient A) X) M.X ≫
      (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map (φ ▷ M.X) ≫
      (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map (Mod.act M.X)).app V).hom
        (r ⊗ₜ[ℤ] m) = _
  erw [← Functor.LaxMonoidal.μ_natural_left_assoc]
  change ((Functor.LaxMonoidal.μ
      (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (FiniteDiscreteOrdinary.coefficient B) X) M.X).app V ≫
      (Mod.act M.X).hom.app V).hom
        ((φ.hom.app V ▷ M.X.obj.obj V).hom (r ⊗ₜ[ℤ] m)) = _
  rw [AddCommGrpCat.MonoidalCategory.whiskerRight_tmul]
  exact congrArg (fun t ↦ ((Functor.LaxMonoidal.μ
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (FiniteDiscreteOrdinary.coefficient B) X) M.X).app V ≫
      (Mod.act M.X).hom.app V).hom (t ⊗ₜ[ℤ] m)) (hn V a)

private def fixed_scalar_change
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    {A B : Type v} [CommRing A] [CommRing B] (f : A →+* B) :
    ConstantCompletion.res ((constantSheaf J CommRingCat.{v}).map (CommRingCat.ofHom f)) ⋙
        coefficientModelFixedScalars J A ≅
      coefficientModelFixedScalars J B ⋙ sheafCompose J (ModuleCat.restrictScalars.{v} f) := by
  let q := (constantSheaf J CommRingCat.{v}).map (CommRingCat.ofHom f)
  have hn (U : Cᵒᵖ) (r : A) :
      q.hom.app U ((toSheafify J ((Functor.const _).obj (CommRingCat.of A))).app U r) =
        (toSheafify J ((Functor.const _).obj (CommRingCat.of B))).app U (f r) := by
    exact (ConcreteCategory.congr_hom (congr_app (toSheafify_naturality J
      ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom f))) U) r).symm
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun r ↦ ?_))
      (by intro U V g; ext x; rfl))) (by intro M N g; ext U x; rfl)
  ext x
  change (toSheafify J ((Functor.const _).obj (CommRingCat.of B))).app U (f r) •
      (show M.val.obj U from x) =
    q.hom.app U ((toSheafify J ((Functor.const _).obj (CommRingCat.of A))).app U r) •
      (show M.val.obj U from x)
  rw [hn]

private def encoding_restriction
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (X : Scheme.{u}) (f : A →+* B)
    (φ : FiniteDiscreteOrdinary.coefficient A ⟶ FiniteDiscreteOrdinary.coefficient B)
    [IsMonHom φ]
    (eA : FiniteDiscreteOrdinary.Encoding A X) (eB : FiniteDiscreteOrdinary.Encoding B X)
    (hp : (Functor.const Profinite.{u}ᵒᵖ).map
        (AddCommGrpCat.ofHom (IntegralSmallPerfect.uliftRingMap f).toAddMonoidHom) ≫
          FiniteDiscreteOrdinary.pointConstants B =
      FiniteDiscreteOrdinary.pointConstants A ≫ φ.hom) :
    Mod.comap ((upperStarFromPoint X).map φ) ⋙
        IntegralFiniteEncoding.finiteEncodingFunctor A X eA ≅
      IntegralFiniteEncoding.finiteEncodingFunctor B X eB ⋙
        ConstantCompletion.res ((constantSheaf
          (Scheme.coefficientProEtaleModelTopology.{u, u} X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom (IntegralSmallPerfect.uliftRingMap f))) := by
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let GA := coefficientModelFixedScalars J (ULift.{u + 1} A)
  let EA := IntegralFiniteEncoding.smallFixedScalarsEquivalence X (ULift.{u + 1} A)
  let EB := IntegralFiniteEncoding.smallFixedScalarsEquivalence X (ULift.{u + 1} B)
  let FA := IntegralFiniteEncoding.finiteEncodingFunctor A X eA
  let FB := IntegralFiniteEncoding.finiteEncodingFunctor B X eB
  let HA := eA.ordinary.functor ⋙ eA.fixed.functor ⋙
    (IntegralFiniteEncoding.smallSiteSheafEquivalence X (ULift.{u + 1} A)).functor
  let HB := eB.ordinary.functor ⋙ eB.fixed.functor ⋙
    (IntegralFiniteEncoding.smallSiteSheafEquivalence X (ULift.{u + 1} B)).functor
  let R : FiniteDiscreteOrdinary.Internal B X ⥤ FiniteDiscreteOrdinary.Internal A X :=
    Mod.comap ((upperStarFromPoint X).map φ)
  let F := sheafCompose J (ModuleCat.restrictScalars.{u + 1} (IntegralSmallPerfect.uliftRingMap f))
  let cA : FA ⋙ GA ≅ HA := Functor.isoWhiskerLeft HA EA.counitIso
  let cB : FB ⋙ coefficientModelFixedScalars J (ULift.{u + 1} B) ≅ HB :=
    Functor.isoWhiskerLeft HB EB.counitIso
  have hn (V : X.ProEtᵒᵖ) (a : ULift.{u + 1} A) :
      ((upperStarFromPoint X).map φ).hom.app V
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
            (FiniteDiscreteOrdinary.canonicalAbelianMap A X).hom).app V a) =
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
            (FiniteDiscreteOrdinary.canonicalAbelianMap B X).hom).app V (ULift.up (f a.down))) := by
    let g := AddCommGrpCat.ofHom (IntegralSmallPerfect.uliftRingMap f).toAddMonoidHom
    have hc := canonical_coefficient_naturality A B X g φ hp
    have hη := toSheafify_naturality (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map g)
    have hη' := ConcreteCategory.congr_hom (congr_app hη V) a
    have h := congrArg (fun t ↦ t.hom.app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app V a)) hc
    change (FiniteDiscreteOrdinary.canonicalAbelianMap B X).hom.app V
      (((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map g).hom.app V
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app V a)) = _ at h
    exact h.symm.trans (congrArg
      ((FiniteDiscreteOrdinary.canonicalAbelianMap B X).hom.app V) hη'.symm)
  let δ : R ⋙ HA ≅ HB ⋙ F := by
    dsimp only [HA, HB]
    rw [eA.ordinary_functor, eA.fixed_functor, eB.ordinary_functor, eB.fixed_functor]
    refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun r ↦ ?_))
        (by intro U V g; ext x; rfl))) (by intro M N g; ext U x; rfl)
    ext x
    exact (encoded_scalar_smul A B X f ((upperStarFromPoint X).map φ) eA eB hn M
      (AsSmall.down.op.obj U) r x).symm
  exact Functor.fullyFaithfulCancelRight GA
    (Functor.isoWhiskerLeft R cA ≪≫ δ ≪≫ Functor.isoWhiskerRight cB.symm F ≪≫
      Functor.isoWhiskerLeft FB (fixed_scalar_change J
        (IntegralSmallPerfect.uliftRingMap f)).symm)

private def extension_of_restriction_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {L' : C ⥤ D} {U' : D ⥤ C}
    {F : A ⥤ C} {G : B ⥤ D} [F.IsEquivalence] [G.IsEquivalence]
    (a : L ⊣ U) (b : L' ⊣ U') (e : U ⋙ F ≅ G ⋙ U') :
    L ⋙ G ≅ F ⋙ L' := by
  let α := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans
  let : IsIso α := CategoryTheory.isIso_inverseMate_of_equivalences a b e
  exact (asIso α).symm

private def encoding_extension
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (X : Scheme.{u}) (f : A →+* B)
    (φ : FiniteDiscreteOrdinary.coefficient A ⟶ FiniteDiscreteOrdinary.coefficient B)
    [IsMonHom φ]
    (eA : FiniteDiscreteOrdinary.Encoding A X) (eB : FiniteDiscreteOrdinary.Encoding B X)
    (hp : (Functor.const Profinite.{u}ᵒᵖ).map
        (AddCommGrpCat.ofHom (IntegralSmallPerfect.uliftRingMap f).toAddMonoidHom) ≫
          FiniteDiscreteOrdinary.pointConstants B =
      FiniteDiscreteOrdinary.pointConstants A ≫ φ.hom) :
    (Mod.extendScalars ((upperStarFromPoint X).map φ)).leftDerivedFunctor ⋙
        IntegralFiniteEncoding.finiteEncodingDerived B X eB ≅
      IntegralFiniteEncoding.finiteEncodingDerived A X eA ⋙
        Scheme.adicFiniteExtension (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (IntegralSmallPerfect.uliftRingMap f) := by
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let q := (constantSheaf J CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (IntegralSmallPerfect.uliftRingMap f))
  let FA := IntegralFiniteEncoding.finiteEncodingFunctor A X eA
  let FB := IntegralFiniteEncoding.finiteEncodingFunctor B X eB
  let U : FiniteDiscreteOrdinary.Internal B X ⥤ FiniteDiscreteOrdinary.Internal A X :=
    Mod.comap ((upperStarFromPoint X).map φ)
  let V := ConstantCompletion.res q
  let : V.Additive := inferInstance
  let : PreservesFiniteLimits V := (siteRestrictScalars_exact q).1
  let : PreservesFiniteColimits V := (siteRestrictScalars_exact q).2
  let sq : U.mapDerivedCategory ⋙ FA.mapDerivedCategory ≅
      FB.mapDerivedCategory ⋙ V.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso U FA).symm ≪≫
      Functor.mapDerivedCategoryNatIso (encoding_restriction A B X f φ eA eB hp) ≪≫
      Functor.mapDerivedCategoryCompIso FB V
  let : (IntegralFiniteEncoding.finiteEncodingDerived A X eA).IsEquivalence :=
    inferInstanceAs FA.mapDerivedCategory.IsEquivalence
  let : (IntegralFiniteEncoding.finiteEncodingDerived B X eB).IsEquivalence :=
    inferInstanceAs FB.mapDerivedCategory.IsEquivalence
  exact extension_of_restriction_square
    (Mod.derivedExtendMapDerivedCategoryAdjunction ((upperStarFromPoint X).map φ))
    (IntegralConstantCompletion.derived_scalar_adjunction q).some sq

private def restricted_level_transition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) (n : ℕ) :
    (AdicCompletion.finiteExtend l E Y n).obj
        ((CondensedRing.upperStar
          (DerivedNakayama.quotientRing l E (n + 2)) f).mapDerivedCategory.obj
           ((AdicCompletion.derivedReduction l E X (n + 1)).obj K)) ≅
      (CondensedRing.upperStar
        (DerivedNakayama.quotientRing l E (n + 1)) f).mapDerivedCategory.obj
         ((AdicCompletion.derivedReduction l E X n).obj K) := by
  let A := DerivedNakayama.quotientRing l E (n + 2)
  let B := DerivedNakayama.quotientRing l E (n + 1)
  let U := CondensedRing.upperStar A f
  let V := CondensedRing.upperStar B f
  let q := AdicCompletion.transitionRing l E n
  let P := (AdicCompletion.derivedReduction l E X (n + 1)).obj K
  let i : U.mapDerivedCategory ⋙ AdicCompletion.finiteExtend l E Y n ≅
      AdicCompletion.finiteExtend l E X n ⋙ V.mapDerivedCategory :=
    Functor.isoWhiskerRight U.leftDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
      CondensedRing.derivedUpperStarExtendScalarsIso q f ≪≫
      Functor.isoWhiskerLeft _ V.leftDerivedFunctorIsoMapDerivedCategory
  exact i.app P ≪≫ V.mapDerivedCategory.mapIso ((AdicCompletion.reductionComp l E X n).app K)

/-- Compatibility of separately obtained finite etale origins.
Source: Stacks Tags 099Y and 09AL; proof step 2 of the integral local structure argument
(blueprint: lem-pe-integral-finite-etale-compatibility).

Normalize the scalar restriction maps on the two consecutive finite coefficient encodings.
The universal property of the corresponding left adjoints identifies the two derived
extensions. Canonical transitivity of the actual reductions gives the comparison on the
pro-etale side; full faithfulness of finite etale comparison lifts it to the chosen origins.
This argument is independent of the existence construction and consumes its output as
explicit hypotheses. -/
theorem integralFiniteEtale_level_compatibility
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [IsImmersion f]
    (K : DerivedCategory (AdicCompletion.Modules l E X)) (a b : ℤ) (hab : a ≤ b)
    (hlevels : ∀ n : ℕ,
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
        ((AdicCompletion.derivedReduction l E X n).obj K) ∧
      DerivedCategory.torAmplitudeIn _ a b ((AdicCompletion.derivedReduction l E X n).obj K))
    (hlisse : ∀ (n : ℕ) (q : ℤ),
      HasFiniteConstantLocalModel (DerivedNakayama.quotientRing l E (n + 1)) Y
        ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) f).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((AdicCompletion.derivedReduction l E X n).obj K))))
 :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ (e : ∀ n : ℕ, FiniteDiscreteOrdinary.Encoding
      (Padic.coefficientExtensionRing l E (n + 1)) Y)
      (C : ∀ n : ℕ, integralFiniteEtaleModel l E Y n)
      (hC : ∀ n : ℕ,
        (∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
          IsZero ((coefficientModelCohomology _ q).obj (C n))) ∧
        (∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
          (Scheme.smallModelComparisonEtaleTopology.{u, u} Y)
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
          ((coefficientModelCohomology _ q).obj (C n))) ∧
        HasCoefficientModelTorAmplitude _ (C n) a b)
      (henc : ∀ n : ℕ, Nonempty
        ((IntegralFiniteEncoding.finiteEncodingDerived
          (Padic.coefficientExtensionRing l E (n + 1)) Y (e n)).obj
            ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1))
              f).mapDerivedCategory.obj
                ((AdicCompletion.derivedReduction l E X n).obj K)) ≅
          (Scheme.adicFinitePullback.{u, u} Y
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).obj (C n))),
      ∀ n : ℕ, Nonempty
        ((Scheme.adicFiniteExtension
          (Scheme.smallModelComparisonEtaleTopology.{u, u} Y)
          (IntegralSmallPerfect.uliftRingMap
            (Padic.coefficientExtensionTransition l E (n + 1)))).obj (C (n + 1)) ≅ C n) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  intro e C hC henc n
  let A := Padic.coefficientExtensionRing l E (n + 2)
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let g : A →+* B := Padic.coefficientExtensionTransition l E (n + 1)
  let g' := IntegralSmallPerfect.uliftRingMap g
  let T := Scheme.smallModelComparisonEtaleTopology.{u, u} Y
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} Y
  let FB := Scheme.adicFinitePullback.{u, u} Y (ULift.{u + 1} B)
  let GE := Scheme.adicFiniteExtension T g'
  let GP := Scheme.adicFiniteExtension J g'
  let P (i : ℕ) :=
    (CondensedRing.upperStar (DerivedNakayama.quotientRing l E (i + 1)) f).mapDerivedCategory.obj
       ((AdicCompletion.derivedReduction l E X i).obj K)
  have hp : (Functor.const Profinite.{u}ᵒᵖ).map
      (AddCommGrpCat.ofHom g'.toAddMonoidHom) ≫ FiniteDiscreteOrdinary.pointConstants B =
        FiniteDiscreteOrdinary.pointConstants A ≫ (AdicCompletion.transitionRing l E n).hom := by
    ext S a
    rfl
  let ce := encoding_extension A B Y g (AdicCompletion.transitionRing l E n)
    (e (n + 1)) (e n) hp
  let ρ : GP.obj ((IntegralFiniteEncoding.finiteEncodingDerived A Y (e (n + 1))).obj
      (P (n + 1))) ≅ (IntegralFiniteEncoding.finiteEncodingDerived B Y (e n)).obj (P n) :=
    (ce.app (P (n + 1))).symm ≪≫
      (IntegralFiniteEncoding.finiteEncodingDerived B Y (e n)).mapIso
        (restricted_level_transition l E f K n)
  let i : FB.obj (GE.obj (C (n + 1))) ≅ FB.obj (C n) :=
    (Scheme.adicFiniteComparison.{u, u} Y g').symm.app (C (n + 1)) ≪≫
      GP.mapIso (henc (n + 1)).some.symm ≪≫ ρ ≪≫ (henc n).some
  let R := ConstantCompletion.constant T (ULift.{u + 1} B)
  let bounded := coefficientCohomologyBounded R
  have hff (K L) (hK : bounded K) (hL : bounded L) :
      Function.Bijective (FB.map : (K ⟶ L) → _) :=
    (coefficientComparison_boundedClassical Y (ULift.{u + 1} B) FB
      (Scheme.adicExactComparison Y (ULift.{u + 1} B))).1 K L hK hL
  have hc : bounded (C n) := by
    obtain ⟨c, d, hc⟩ := (hC n).1
    exact ⟨min c d, d, min_le_right _ _, fun q hq ↦ hc q (by
      rcases hq with hq | hq
      · exact Or.inl (lt_of_lt_of_le hq (min_le_left _ _))
      · exact Or.inr hq)⟩
  have he : bounded (GE.obj (C (n + 1))) :=
    ⟨a, b, hab, Scheme.adicScalarExtension_bound T g' (C (n + 1)) a b
      (hC (n + 1)).2.2⟩
  obtain ⟨t, _⟩ := Scheme.liftIsoOnProperty FB bounded hff _ _ he hc i
  exact ⟨t⟩

/-- Finite levels with lisse finite cohomology have compatible normalized etale origins.
The statement concerns only finite coefficient complexes and their quotient maps.
Source: current blueprint, sk-prop-integral-local-structure, proof step 2;
Stacks Tags 099Y and 09AL
(blueprint: lem-pe-integral-finite-etale-models).

Proof: choose the normalized finite coefficient section-action encoding at each positive
level. Its exactness identifies homology with encoded homology. Its monoidal comparison
preserves the given Tor interval. Pullback to the stratum preserves these assertions;
the finite local model comparison makes every encoded cohomology sheaf lisse of finite
type. Transport to the coefficient-sized site and undo constant-scalar restriction.
Constructible etale comparison and finite-Tor comparison give the etale origins, the
same bounds and lissity. Normalization on constant scalar sections identifies restriction
along consecutive quotient maps on both sides of the encoding. Their left adjoints
therefore identify derived extension. The canonical transitivity isomorphism for the
actual reductions gives the consecutive maps after encoding. Full faithfulness of etale
comparison lifts them to the asserted etale isomorphisms. No compatible local constant
markings, completeness of a scalar model, or integral reconstruction is used. All
arguments apply to empty strata; positive quotient levels have their actual discrete
topology, including the zero-ring case. -/
theorem integralFiniteEtale_models
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [IsImmersion f]
    (K : DerivedCategory (AdicCompletion.Modules l E X)) (a b : ℤ) (hab : a ≤ b)
    (hlevels : ∀ n : ℕ,
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
        ((AdicCompletion.derivedReduction l E X n).obj K) ∧
      DerivedCategory.torAmplitudeIn _ a b ((AdicCompletion.derivedReduction l E X n).obj K))
    (hlisse : ∀ (n : ℕ) (q : ℤ),
      HasFiniteConstantLocalModel (DerivedNakayama.quotientRing l E (n + 1)) Y
        ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) f).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((AdicCompletion.derivedReduction l E X n).obj K)))) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∃ (e : ∀ n : ℕ, FiniteDiscreteOrdinary.Encoding
          (Padic.coefficientExtensionRing l E (n + 1)) Y)
      (C : ∀ n : ℕ, integralFiniteEtaleModel l E Y n),
      (∀ n : ℕ,
        (∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
          IsZero ((coefficientModelCohomology _ q).obj (C n))) ∧
        (∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
          (Scheme.smallModelComparisonEtaleTopology.{u, u} Y)
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
          ((coefficientModelCohomology _ q).obj (C n))) ∧
        HasCoefficientModelTorAmplitude _ (C n) a b) ∧
      (∀ n : ℕ, Nonempty
        ((Scheme.adicFiniteExtension (Scheme.smallModelComparisonEtaleTopology.{u, u} Y)
          (IntegralSmallPerfect.uliftRingMap
            (Padic.coefficientExtensionTransition l E (n + 1)))).obj (C (n + 1)) ≅ C n)) ∧
      ∀ n : ℕ, Nonempty
        ((IntegralFiniteEncoding.finiteEncodingDerived
          (Padic.coefficientExtensionRing l E (n + 1)) Y (e n)).obj
            ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1))
              f).mapDerivedCategory.obj
                ((AdicCompletion.derivedReduction l E X n).obj K)) ≅
          (Scheme.adicFinitePullback.{u, u} Y
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).obj (C n)) := by
  let _ := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  obtain ⟨e, C, hC, henc⟩ := integralFiniteEtale_level_models l E f K a b hab hlevels hlisse
  have hβ := integralFiniteEtale_level_compatibility
    l E f K a b hab hlevels hlisse e C hC henc
  exact ⟨e, C, hC, hβ, henc⟩

end AlgebraicGeometry.ProEtale
