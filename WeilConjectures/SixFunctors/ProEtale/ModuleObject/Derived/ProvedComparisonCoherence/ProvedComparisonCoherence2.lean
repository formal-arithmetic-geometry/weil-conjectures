/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
public import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ScalarPullbackMateInverseNormalized
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidalComp
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp
public import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedDualizableIndependent
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalIhom

public import WeilConjectures.SmoothPurity.CoefFiniteHom
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralHom.CondensedIntegralHomReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.ConstructibleSheaf.Devissage
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
public import Mathlib.RingTheory.Finiteness.Projective
public import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
public import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
public import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionModuleOperationsData
public import WeilConjectures.AlgebraicGeometry.FiniteCondensedVerdierComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleFamilyModels
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
public import WeilConjectures.ConstructibleSheaf.FreeLifting
public import WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldFiniteTorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Affine.AffineEtaleFreeDetection
public import Mathlib.CategoryTheory.Skeletal
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.FiniteRingGeometricDualityFiniteField
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedNakayamaFirstReduction
public import WeilConjectures.AlgebraicGeometry.PrincipalTensorScalarExtension
public import Mathlib.Algebra.Homology.Double
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentObjects
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentHom
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductionsStatement
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.AlgebraicGeometry.IntegralSectionLocalModels
public import WeilConjectures.AlgebraicGeometry.IntegralSectionMemberModels
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeTensor
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeHom
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedVerdierExchange
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import Mathlib.Tactic.DefEqTransformations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.CategoryTheory.FiniteCondensedNormalizedAdjunction
public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Triangulated.Opposite.OpOp
public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCtfSixFunctorStabilityCurrent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AllCoefficientProjection.CondensedAllCoefficientProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
public import WeilConjectures.SmoothPurity.CurrentExceptionalAdjointAdmissibility
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteReductionOfPurity2
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDualityConventionsCondensed
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.AlgebraicGeometry.Picard.Purity.Condensed.NativeCompactSupportWeilTransport
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFrobeniusComparisonCoherence
public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportPull
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit
public import WeilConjectures.Compactification.CommonDenseRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactScalarPointCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
public import WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ScalarChangeAdjunctions
public import WeilConjectures.CategoryTheory.Monoidal.Closed.PairingComparison
public import WeilConjectures.DeligneLaumon.WeilOperations.WeilOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.CondensedVerdierWeilEquivariance
public import WeilConjectures.AlgebraicGeometry.Picard.PurityWeil.Compatibilities.WeilEquivarianceCompatibilities

/-! # Coherence of the proved condensed comparison maps

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/
sk-d-proper-pushforward/sk-thm-sf-compatibility/fix-prop-coherence.md and its six-step
assembly proof
(blueprint: fix-prop-coherence).

## Main definitions

* The clause propositions below name the individual canonical comparison equations.
* `Laws` packages all those clauses as a proposition.

## Main statements

* `coherence` states all the laws on the domains of the proved comparison maps.

Each clause below is an explicit proposition about the existing canonical maps.
These definitions only package the clauses of this assembly theorem. They introduce
no operation, coefficient category, comparison map, or choice of an isomorphism.
In particular exceptional comparisons use the current restricted Brown adjunctions;
Weil statements use condensed pairs and no triangulated structure on their category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u

open Opposite
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor CategoryTheory.TwoSquare
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.ProvedComparisonCoherence

section
open CompactSupportComposition

end

section

end

section
open WeilConjectures

end

section
open AlgebraicGeometry.ProEtale.CondensedIntegralHom

end

section

end

section

end

section

end

section

end

section

end

section

end

section
open AlgebraicGeometry.ProEtale.CondensedRing.AllCoefficientProjection
open CompactSupportComposition CompactificationReindexing

end

section
open AlgebraicGeometry.ProEtale.CondensedRing.AllCoefficientProjection
open CompactSupportComposition CompactificationReindexing

end

section
open AlgebraicGeometry.ProEtale.CondensedRing.AllCoefficientProjection
open CompactSupportComposition CompactificationReindexing

end

section
open AlgebraicGeometry.ProEtale.CondensedRing.AllCoefficientProjection
open CompactSupportComposition CompactificationReindexing

end

section
open AlgebraicGeometry.Etale AlgebraicGeometry.Etale.AllCoefficientProjection

/-- Finite projection, naturality, scalar reduction, compactification and proper coincidence.
Source: fix-prop-coherence, the clause supplied by `finite`
in `Sheaf.Paper.CondensedAllCoefficientProjectionFormula` (blueprint: fix-prop-coherence). -/
def finiteProjection : Prop :=
  ∀ (D₀ : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D₀.p) (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D₀.k))] [Y.Over (Spec (.of D₀.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D₀.k))] [QuasiCompact (X ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D₀.k))] [QuasiCompact (Y ↘ Spec (.of D₀.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D₀.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) X) (L :
        DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) Y)
    (hK : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing ell E n) X K)
    (hL : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing ell E n) Y L)
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing ell E n)
        Y a b L),
    (type_of% (isIso_finiteCompactProjection D₀ ell hell E n f c K L hK hL hTor)) ∧
    (∀ (K' : DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) X) (L' :
        DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) Y)
      (a : K ⟶ K') (b : L ⟶ L'),
      type_of% (WeilConjectures.sixFunctorProjection_naturality (Padic.coefficientExtensionRing
        ell E n) c a b)) ∧
    (∀ d : Compactification f,
      type_of% (WeilConjectures.sixFunctorProjection_compactification
        (Padic.coefficientExtensionRing ell E n) c d K L)) ∧
    (∀ (_hKTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing ell E n) X a b K)
      (J : Ideal (Padic.coefficientExtensionRing ell E n))
      (_hJ : ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ Nonempty
        ((Padic.coefficientExtensionRing ell E n ⧸ J) ≃+*
          Padic.coefficientExtensionRing ell E m)),
      type_of% (WeilConjectures.sixFunctorProjection_reduction_finite
        (Padic.coefficientExtensionRing ell E n) c J K L)) ∧
    (∀ [IsProper f],
      type_of% (WeilConjectures.sixFunctorProjection_proper (Padic.coefficientExtensionRing ell E
        n) f K L))

end

section
open AlgebraicGeometry.Etale AlgebraicGeometry.Etale.AllCoefficientProjection
open AlgebraicGeometry.ProEtale.CondensedRing.CompactSupportComposition

/-- Finite projection composition and its canonical associativity pentagon.
Source: fix-prop-coherence, the clause supplied by `finiteComposition`
in `Sheaf.Paper.CondensedAllCoefficientProjectionFormula` (blueprint: fix-prop-coherence). -/
def finiteProjectionComposition : Prop :=
  ∀ (D₀ : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) [Fact (1 ≤ n)]
    (_hell : ell ≠ D₀.p) {X Y Z T : SepFinType D₀.k}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (d : Compactification g.hom.left)
    (e : Compactification (f.hom.left ≫ d.i))
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) X.obj.left)
    (L : DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) Z.obj.left)
    (_hK : DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing ell E n) X.obj.left K)
    (_hL : DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing ell E n) Z.obj.left L)
    (_hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing ell E n) Z.obj.left a b L),
    (type_of% (WeilConjectures.sixFunctorProjection_composition
      (Padic.coefficientExtensionRing ell E n) f.hom.left g.hom.left d e K L)) ∧
    finitePentagonAssertions (Padic.coefficientExtensionRing ell E n) f g h

end

section
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AllCoefficientProjection

/-- The specified finite projection on the intrinsic pro-etale bounded-constructible domain.
Source: fix-prop-coherence, the clause supplied by `finite`
in `Sheaf.Paper.CondensedAllCoefficientProjectionFormula` (blueprint: fix-prop-coherence). -/
def intrinsicFiniteProjection : Prop :=
  ∀ (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D₀.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : SepFinType D₀.k} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
    (_hK : DerivedCategory.boundedConstructibleIntrinsic
      (Padic.coefficientExtensionRing ell E n) X.obj.left K)
    (_hL : DerivedCategory.boundedConstructibleIntrinsic
      (Padic.coefficientExtensionRing ell E n) Y.obj.left L)
    (_hTor : ∃ a b : ℤ, DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n)) Y.obj.left a b L),
    IsIso (((projectionMapOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n)) c).app K).app L)

end

section
open AlgebraicGeometry.ProEtale.QuotientChange

end

section

end

section

end

section

end

section
open CompactificationReindexing

/-- Canonical common-refinement-normalized comparisons identify the two compact-support exchange
maps.
Source: fix-prop-coherence, the clause supplied by `exchangeProjection_compactification_independent`
in `Sheaf.SmoothPurity.ExchangeProjection` (blueprint: fix-prop-coherence). -/
def exchangeRefinement : Prop :=
  ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n : ℕ) (_hn : 1 ≤ n)
    (_hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (properOpenFiniteCoefficient ℓ E n)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (properOpenIntegralCoefficient ℓ E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (properOpenFieldCoefficient ℓ E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (S : Scheme.{u}) (_hℓ : ∀ s : S, IsUnit (ℓ : S.residueField s))
    {X Y Y' : Scheme.{u}}
    [X.Over S] [Y.Over S] [Y'.Over S]
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    [LocallyOfFiniteType (Y' ↘ S)] [QuasiCompact (Y' ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (v : Y' ⟶ Y) [v.IsOver S] [IsSeparated v]
    [LocallyOfFiniteType v] [QuasiCompact v],
    ∃ τ : ∀ c₁ c₂ : Compactification f,
        (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₁ ≅
          (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₂,
      ∃ τ' : ∀ c₁ c₂ : Compactification f,
        (boundedConstructible (condensedRingObj Λ X)).ι ⋙
            P Λ (pullback.fst f v) ⋙ F Λ (c₁.baseChange v) ≅
          (boundedConstructible (condensedRingObj Λ X)).ι ⋙
            P Λ (pullback.fst f v) ⋙ F Λ (c₂.baseChange v),
        (∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
            (h₂ : d.Refinement c₂)
            (K : BoundedConstructible (condensedRingObj Λ X)),
          (τ c₁ c₂).hom.app K ≫ (refinement Λ h₂).app K.obj =
            (refinement Λ h₁).app K.obj) ∧
        (∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
            (h₂ : d.Refinement c₂)
            (K : BoundedConstructible (condensedRingObj Λ X)),
          (τ' c₁ c₂).hom.app K ≫
              (refinement Λ (refinementBaseChange h₂ v)).app
                ((P Λ (pullback.fst f v)).obj K.obj) =
            (refinement Λ (refinementBaseChange h₁ v)).app
              ((P Λ (pullback.fst f v)).obj K.obj)) ∧
        (∀ (c₁ c₂ : Compactification f)
            (K : BoundedConstructible (condensedRingObj Λ X)),
          (P Λ v).map ((τ c₁ c₂).hom.app K) ≫
              (exchangeProjectionData Λ c₂ v).compact.app K.obj =
            (exchangeProjectionData Λ c₁ v).compact.app K.obj ≫
              (τ' c₁ c₂).hom.app K)

end

section
open CurrentVerdierExchange

end

section
open AlgebraicGeometry.Etale.FiniteSmoothPurity

end

section
open AlgebraicGeometry.Etale.FiniteSmoothPurity

end

section
open AlgebraicGeometry.Etale.FiniteSmoothPurity

end

section
open AlgebraicGeometry.Etale.FiniteSmoothPurity

end

section
open AlgebraicGeometry.Etale.FiniteSmoothPurity

end

section
open AlgebraicGeometry.Etale.FiniteSmoothPurity

end

section
open WeilConjectures WeilConjectures.PoincareFiniteReduction
open AlgebraicGeometry.ProEtale.PurityTransport

end

section
open WeilConjectures

end

section
open StrictWeilCondensed
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed

end

section
open AlgebraicGeometry.ProEtale.PurityTransport
open WeilConjectures.PurityWeil WeilConjectures.PurityWeil.Condensed
open WeilConjectures.Purity.Condensed WeilConjectures.PurityWeil.Compatibilities

end

section
open AlgebraicGeometry.ProEtale.QuotientChange

end

/-- The existing operations and their proved comparison maps satisfy coherence.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/
sk-d-proper-pushforward/sk-thm-sf-compatibility/fix-prop-coherence.md and .proof.md
(blueprint: fix-prop-coherence).

Proof plan, in the six steps of the node:
1. Use the canonical exchange identity and horizontal/vertical mate-pasting laws.
   Compact-support composition, common-refinement normalization and the projection
   formula supply the associativity pentagon, projection diamonds and proper coincidence
   (fix-lem-exchanges, fix-prop-projection-formula, def-fix-six-functor-datum).
2. The elementary comparison maps preserve tensor reassociation, evaluation, and
   adjunction units and counits (lem-fix-operation-reduction). Paste these actual
   squares, using naturality when a defining factor is mapped by an operation.
3. The finite-Tor Hom, integral Hom and integral finite-extension comparisons are
   transposes of the same scalar-extended evaluations. Their unit and scalar tower
   equations extend the elementary equations on every stated overlap
   (thm-coef-finite-hom, lem-coef-integral-hom-reduction,
   lem-coef-integral-finite-extension).
4. On Dctf the finite exceptional and scalar-six comparisons preserve both adjunction
   equations (lem-coef-finite-exceptional, sk-prop-scalar-six, sk-thm-existence).
   The Hom bijection therefore identifies the compared transpose with the transpose
   of the compared arrow. Apply this to the specified Verdier exchange
   (fix-cor-verdier-exchange); no ambient exceptional adjoint is assumed.
5. Retain the normalized purity, affine orientation, trace, composition and base-change
   squares (thm-pur-finite-reduction-of-purity). Compose with evaluation to obtain the
   site-perfect pairing equation and its inverse-adjoint square
   (thm-pod-finite-reduction).
6. The algebraic operations and duality comparisons are Weil-equivariant
   (lem-fix-weil-operations, cor-coef-verdier-weil-equivariance). Composition preserves
   their equivariance equations. Use prop-pur-weil-equivariance-compatibilities for
   the additional geometric- and scheme-Frobenius purity squares. No new preservation
   or biduality statement, or triangulated structure on Weil pairs, is inferred.
-/
theorem coherence : Laws.{u} := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.ProvedComparisonCoherence
