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
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).obj (C n)) := by sorry

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
            (Padic.coefficientExtensionTransition l E (n + 1)))).obj (C (n + 1)) ≅ C n) := by sorry

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
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).obj (C n)) := by sorry

end AlgebraicGeometry.ProEtale
