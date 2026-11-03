/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SmoothPurity.FiniteRingTrace.FiniteRingTraceDualizingComplex
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfLocallyClosedPerfectGeneration
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompactSupportUniformRestriction
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientProjectionDataSupplement
import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization
import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackShifts
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientScalarUnits
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions
import WeilConjectures.ProperBaseChange.CondensedERealizationSystem
import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedEIntegralExchange
import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERationalCondensedExchange
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedCompactSupportProjection
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization
import WeilConjectures.SixFunctors.GeneratorReduction.ConstantSemilinearGeneratorComparison
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
import WeilConjectures.AlgebraicGeometry.Sf.SfCbcCompactSupportCompositionLimit
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.Compactification.Triangle
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenPasting
import WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity
import WeilConjectures.SixFunctors.IntegralSystemRealization.CompletedShriekCompositionLaws
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealization
import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionZeroCompletion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionStatement
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationSheafExact
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientGeneralPullbackIso
import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.ProEtaleCoefficients.CompletedCoefficientCompletionRoosTransportLegacy
import Mathlib.Data.Nat.Prime.Infinite
import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompCompositionBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedLocalization
import WeilConjectures.PoincareDuality.ProjectionFormula
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ModuleRingedToposDerivedComparison
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
import WeilConjectures.SixFunctors.Finite.FiniteConstructibleHom
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowDerivedSmoothBaseChange
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorShifts
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDualizableHomWindow
import WeilConjectures.AlgebraicGeometry.CondensedBoundedOpenOperations
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperConstructibleProjection
import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Monoidal.Subcategory
import WeilConjectures.CategoryTheory.Projection.ProjectionInternalHom
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionConstantModelConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
import WeilConjectures.SixFunctors.Etale.Derived.RationalStage
import WeilConjectures.SixFunctors.Sf.SfBidualityClass
import Mathlib.Topology.KrullDimension
import WeilConjectures.CategoryTheory.FiniteCondensedNormalizedAdjunction
import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteCondensedVerdierComparison
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullback
import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
import Mathlib.Algebra.Field.ULift
import WeilConjectures.CategoryTheory.RingObjects.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedVerdierScalarTransport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedVerdierCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Internal.InternalFirstResidueRingIsoSupplement
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import all WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing

/-! # Support products and base change along the other leg

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/
lem-trf-trace-class-diagonal-pairing.proof.md, Step 4
(blueprint: lem-trf-support-product-base-change).

The support recipe of def-trf-supported-pairing, Step 2, is used on an arbitrary
Cartesian square. The unit-normalized projection arrow is the published
`projectionUnitMap`: its inverse inserts the unit before inverse projection formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.TrfSupportProduct

namespace Data

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

local instance coefficientFinite : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)

/-- The finite discrete coefficient, using the library's coefficient convention.
Source: def-trf-coefficient-conventions (blueprint: lem-trf-support-product-base-change). -/
abbrev Coefficients := FiniteRingTrace.coefficient.{u}
  (Padic.coefficientExtensionRing l E (n + 1))

/-- The ordinary module-derived category, without a new realization.
Source: Step 4 (blueprint: lem-trf-support-product-base-change). -/
abbrev Ambient (T : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (Coefficients l E n) T))

/-- The intrinsic finite-Tor constructible category, retaining the previous domain.
Source: prop-functor-package (blueprint: lem-trf-support-product-base-change). -/
abbrev Ctf (T : Scheme.{u}) := CondensedConstructibleFiniteTor (Coefficients l E n) T

/-- The original total derived inverse image.
Source: Step 4 (blueprint: lem-trf-support-product-base-change). -/
abbrev pull {T U : Scheme.{u}} (f : T ⟶ U) :=
  moduleObjectDerivedPullback (Coefficients l E n) f

/-- The signed derived braiding.
Source: Step 4 (blueprint: lem-trf-support-product-base-change). -/
abbrev braiding (T : Scheme.{u}) : BraidedCategory (Ambient l E n T) :=
  DerivedCategory.braidedCategory' _

/-- The coefficient-unit comparison for the library's degree-zero regular module.
Source: Step 4 (blueprint: lem-trf-support-product-base-change). -/
def coefficientUnitIso (T : Scheme.{u}) :
    constantCoefficientObject (Coefficients l E n) T ≅ 𝟙_ (Ambient l E n T) :=
  DerivedCategory.singleFunctorObjUnitIso _

/-- The positive quotient is killed by a power of ell.
Source: def-trf-coefficient-conventions (blueprint: lem-trf-support-product-base-change).
Proof: ell belongs to the maximal ideal of the integer ring. Its (n+1)-st power is
in the (n+1)-st power of that ideal, which defines the quotient. Multiplication by
this zero scalar annihilates every element. -/
theorem coefficientKilled : ∃ r : ℕ, ∀ a : Padic.coefficientExtensionRing l E (n + 1),
    (l ^ r) • a = 0 := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) := by
    rw [hgen]
    apply (h.2.1 _).mpr
    change spectralNorm ℚ_[l] E (l : E) < 1
    simpa only [map_natCast] using
      (spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])).trans_lt
        (Padic.norm_p_lt_one)
  have hpow := Ideal.pow_mem_pow hlm (n + 1)
  have hz : (l : Padic.coefficientExtensionRing l E (n + 1)) ^ (n + 1) = 0 := by
    simpa only [map_pow, map_natCast] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr hpow)
  refine ⟨n + 1, fun a ↦ ?_⟩
  simp only [nsmul_eq_mul, Nat.cast_pow, hz, zero_mul]

/-- These finite discrete coefficients satisfy the library's admissibility predicate.
Source: coefficient conventions (blueprint: lem-trf-support-product-base-change).
Proof: use the quotient itself as the finite ring, with its discrete topology,
coefficientKilled as annihilation, and the identity coefficient-ring comparison. -/
theorem coefficientAdmissible : IsLocalizingAdmissibleCoefficient l (Coefficients l E n) := by
  let : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  let : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  let : IsTopologicalRing (Padic.coefficientExtensionRing l E (n + 1)) :=
    DiscreteTopology.topologicalRing
  exact Or.inl ⟨_, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, coefficientKilled l E n, ⟨Iso.refl _⟩⟩

variable {F : FiniteFieldDatum.{u}} [Fact (l ≠ F.p)]

local instance fieldCharacteristic : CharP F.k F.p := FiniteRingTrace.fieldChar F
local instance primeCharacteristic : Fact F.p.Prime := ⟨F.prime⟩
local instance primeRingCharacteristic : Fact (ringChar F.k).Prime :=
  ⟨(ringChar.eq F.k F.p).symm ▸ F.prime⟩
local instance differentCharacteristic : Fact (ringChar F.k ≠ l) :=
  ⟨(ringChar.eq F.k F.p).symm ▸ (Fact.out : l ≠ F.p).symm⟩

variable {l E n}

local instance structureLft (T : SepFinType F.k) :
    LocallyOfFiniteType (T.obj.left ↘ Spec (.of F.k)) := by
  change LocallyOfFiniteType T.obj.hom
  infer_instance
local instance structureQc (T : SepFinType F.k) :
    QuasiCompact (T.obj.left ↘ Spec (.of F.k)) := by
  change QuasiCompact T.obj.hom
  infer_instance
local instance structureSeparated (T : SepFinType F.k) :
    IsSeparated (T.obj.left ↘ Spec (.of F.k)) := by
  change IsSeparated T.obj.hom
  infer_instance
local instance structureCompact (T : SepFinType F.k) : CompactSpace T.obj.left :=
  QuasiCompact.compactSpace_of_compactSpace (T.obj.left ↘ Spec (.of F.k))
local instance structureQuasiSeparated (T : SepFinType F.k) :
    QuasiSeparatedSpace T.obj.left :=
  quasiSeparatedSpace_of_quasiSeparated (T.obj.left ↘ Spec (.of F.k))
local instance arrowSeparated {T U : SepFinType F.k} (f : T ⟶ U) : IsSeparated f.hom.left := by
  have : IsSeparated (f.hom.left ≫ U.obj.hom) := by
    rw [Over.w f.hom]
    infer_instance
  exact IsSeparated.of_comp f.hom.left U.obj.hom
local instance arrowLft {T U : SepFinType F.k} (f : T ⟶ U) :
    LocallyOfFiniteType f.hom.left := by
  have : LocallyOfFiniteType (f.hom.left ≫ U.obj.hom) := by
    rw [Over.w f.hom]
    infer_instance
  exact locallyOfFiniteType_of_comp f.hom.left U.obj.hom
local instance arrowQc {T U : SepFinType F.k} (f : T ⟶ U) : QuasiCompact f.hom.left := by
  have : QuasiCompact (f.hom.left ≫ U.obj.hom) := by
    rw [Over.w f.hom]
    infer_instance
  exact QuasiCompact.of_comp f.hom.left U.obj.hom

/-- The same fixed Nagata compactification, obtained directly from the library.
Source: support recipe Step 2 (blueprint: lem-trf-support-product-base-change). -/
abbrev supportCompactification {T U : SepFinType F.k} (f : T ⟶ U) :=
  (AlgebraicGeometry.compactificationOverField F.k f.hom.left).obj.obj

/-- The preservation witness belonging to the simultaneous coherent comparisons.
Source: prop-functor-package (3) (blueprint: lem-trf-support-product-base-change). -/
abbrev supportPreserves {X Y : SepFinType F.k} (f : X ⟶ Y)
    (c : Compactification f.hom.left) := (supportCoherence (F := F) l E n).choose f c

/-- The normalized composition family from that same coherent witness.
Source: prop-functor-package (3) (blueprint: lem-trf-support-product-base-change). -/
abbrev supportComp {X Y Z : SepFinType F.k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f.hom.left) (d : Compactification g.hom.left)
    (e : Compactification (f.hom.left ≫ g.hom.left)) :=
  (supportCoherence (F := F) l E n).choose_spec.choose_spec.choose f g c d e

/-- The normalized Cartesian exchange from that same coherent witness.
Source: prop-functor-package (4) (blueprint: lem-trf-support-product-base-change). -/
abbrev supportExchange {X Y X' Y' : SepFinType F.k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback a f'.hom.left f.hom.left v)
    (c : Compactification f.hom.left) (d : Compactification f'.hom.left) :=
  let h := supportCoherence (F := F) l E n
  h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose sq c d

/-- Compact support in the fixed compactification model.
Source: support recipe Step 2 (blueprint: lem-trf-support-product-base-change). -/
abbrev spLower {T U : SepFinType F.k} (f : T ⟶ U) :=
  rightDerivedLowerShriekOfCompactification (Coefficients l E n) (supportCompactification f)

/-- The degree-zero regular coefficient object.
Source: support recipe Step 2 (blueprint: lem-trf-support-product-base-change). -/
abbrev spUnit (T : SepFinType F.k) := constantCoefficientObject (Coefficients l E n) T.obj.left

/-- The regular coefficient lies in Dctf.
Source: support recipe Step 2 (blueprint: lem-trf-support-product-base-change). -/
abbrev spUnitCtf (T : SepFinType F.k) :
    ConstantModelConstructibleFiniteTor (Coefficients l E n) T.obj.left :=
  ⟨spUnit (l := l) (E := E) (n := n) T,
    constantCoefficientObject_mem (Coefficients l E n) T.obj.left⟩

/-- Its inclusion in the localizing closure.
Source: prop-functor-package (3)--(4) (blueprint: lem-trf-support-product-base-change). -/
abbrev spUnitLoc (T : SepFinType F.k) :
    (localizingClosureProEtale (Coefficients l E n) T.obj.left).FullSubcategory :=
  ⟨spUnit (l := l) (E := E) (n := n) T, fun _P _hP hS ↦ hS _
    (constantCoefficientObject_mem _ T.obj.left)⟩

/-- Native and finite constant-model Dctf have exactly the same objects here.
Source: finite coefficient comparison (blueprint: lem-trf-support-product-base-change).
Proof: the common finite-discrete encoding sends an intrinsic constructible sheaf to
an ordinary finite constructible sheaf. The proved constant-model comparison sends
it back to a finite constant model; its counit identifies the result with the original
sheaf. Conversely constant models are locally finitely presented on the same strata.
Apply this in every homology degree; boundedness and finite Tor are unchanged. -/
theorem nativeCtf_iff (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (K : Ambient l E n T) :
    condensedConstructibleFiniteTor (Coefficients l E n) T K ↔
      (constantModelBoundedConstructible (Coefficients l E n) T ⊓
        DerivedCategory.finiteTorAmplitude _) K := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : IsTopologicalRing A := DiscreteTopology.topologicalRing
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} A
  let : IsMonHom eR.hom := heR
  let G := internalToModule (ULift.{u + 1} A)
  let e := finiteDiscreteCoefficientEquivalence A eR G rfl T
  have hc (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Coefficients l E n) T)) :
      IsConstructibleModuleObject (condensedRingObj (Coefficients l E n) T) M ↔
        IsConstantModelConstructible (Coefficients l E n) T M := by
    constructor
    · intro hM
      have hF := finiteDiscreteCoefficient_constructible A eR G rfl T M hM
      have hE := (encoding_constructible_iff A T eR (e.inverse.obj M)).mp hF
      have : ObjectProperty.IsClosedUnderIsomorphisms
          (IsConstantModelConstructible (Coefficients l E n) T) :=
        (constantModelConstructibleFiniteTor_wellDefined (Coefficients l E n) T).1
      exact ObjectProperty.prop_of_iso
        (IsConstantModelConstructible (Coefficients l E n) T)
        (e.counitIso.app M) hE
    · intro hM
      rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hM
      exact modelStratifiedConstructible (Coefficients l E n) T M hM
  change (_ ∧ (∀ q, _)) ∧ _ ↔ (_ ∧ (∀ q, _)) ∧ _
  exact and_congr (and_congr Iff.rfl (forall_congr' fun q ↦ hc _)) Iff.rfl

/-- Projection followed by the unit constraint, with the published arrow and its direction.
Source: prop-functor-package (5) (blueprint: lem-trf-support-product-base-change). -/
def projectionUnitMap {T U : SepFinType F.k} (f : T ⟶ U) (M : Ambient l E n U.obj.left) :
    (spLower (l := l) (E := E) (n := n) f).obj (𝟙_ _) ⊗ M ⟶
      (spLower (l := l) (E := E) (n := n) f).obj ((pull l E n f.hom.left).obj M) :=
  exceptionalProjectionMorphismOfCompactification (Coefficients l E n)
      (supportCompactification f) (𝟙_ _) M ≫
    (spLower (l := l) (E := E) (n := n) f).map
      (λ_ ((pull l E n f.hom.left).obj M)).hom

/-- Invertibility of exactly that projection, on the library's stated Dctf domain.
Source: prop-functor-package (5) (blueprint: lem-trf-support-product-base-change).
Proof: the regular coefficient is bounded constructible by its Dctf certificate;
apply the projection field of condensedFunctorPackage to that object and M, then
compose with compact support applied to the left unitor. -/
theorem projectionUnit_isIso {T U : SepFinType F.k} (f : T ⟶ U)
    (M : Ctf l E n U.obj.left) : IsIso (projectionUnitMap f M.obj) := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (constantModelBoundedConstructible (Coefficients l E n) T.obj.left) :=
    (constantModelConstructibleFiniteTor_wellDefined (Coefficients l E n) T.obj.left).2.1
  have := (condensedFunctorPackage l F).projection (Coefficients l E n)
    (coefficientAdmissible l E n) f.hom (supportCompactification f)
    ⟨𝟙_ _, (constantModelBoundedConstructible (Coefficients l E n) T.obj.left).prop_of_iso
      (coefficientUnitIso l E n T.obj.left) (spUnitCtf (l := l) (E := E) (n := n) T).property.1⟩
    ⟨M.obj, (nativeCtf_iff U.obj.left M.obj).mp M.property⟩
  unfold projectionUnitMap
  infer_instance

end Data

attribute [local instance] Data.structureLft Data.structureQc Data.structureSeparated
  Data.structureCompact Data.structureQuasiSeparated Data.arrowLft Data.arrowQc Data.arrowSeparated
open Data

variable {F : FiniteFieldDatum.{u}} {l : ℕ} [Fact l.Prime]
  {E : Type} [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {n : ℕ} [Fact (l ≠ F.p)]
  {B U V T : SepFinType F.k}

/-- Constant pullback along any leg, with the regular coefficient object of the pairing.
Source: Step 4, constant pullback identifications
(blueprint: lem-trf-support-product-base-change). -/
def unitPull (r : T ⟶ V) :
    (pull l E n r.hom.left).obj (spUnit (l := l) (E := E) (n := n) V) ≅
      spUnit (l := l) (E := E) (n := n) T :=
  (pull l E n r.hom.left).mapIso
      (coefficientUnitIso l E n V.obj.left) ≪≫
    leftDerivedUpperStarUnitIso (Coefficients l E n) r.hom.left ≪≫
    (coefficientUnitIso l E n T.obj.left).symm

/-- The compactly supported constant object belongs to Dctf, with its unchanged ambient
object. Source: prop-functor-package (3)--(5), the domain used in Step 4
(blueprint: lem-trf-support-product-base-change). -/
def supportCtf (f : U ⟶ B) : Ctf l E n B.obj.left :=
  ⟨(spLower (l := l) (E := E) (n := n) f).obj
      (spUnit (l := l) (E := E) (n := n) U),
    (nativeCtf_iff B.obj.left _).mpr
      ((supportPreserves (F := F) (l := l) (E := E) (n := n) f
        (supportCompactification f)).2 _
          (spUnitCtf (l := l) (E := E) (n := n) U).property)⟩

/-- `π_g(N)`: signed symmetry, replacement of the regular coefficient by the tensor
unit, and the published projection map followed by the unit constraint.
Source: Step 4, the projection formula for the other leg
(blueprint: lem-trf-support-product-base-change). -/
def projectionOtherLeg (g : V ⟶ B) (N : Ambient l E n B.obj.left) :
    N ⊗ (spLower (l := l) (E := E) (n := n) g).obj
        (spUnit (l := l) (E := E) (n := n) V) ⟶
      (spLower (l := l) (E := E) (n := n) g).obj ((pull l E n g.hom.left).obj N) :=
  letI := braiding l E n B.obj.left
  (β_ _ _).hom ≫
    ((spLower (l := l) (E := E) (n := n) g).map
      (coefficientUnitIso l E n V.obj.left).hom ▷ N) ≫
    projectionUnitMap g N

/-- The stipulated `μ`: inverse composition, constant pullback, inverse exchange along
`f`, then inverse unit-normalized projection, and conversion back to `A_U`.
Source: def-trf-supported-pairing Step 2 and diagonal-pairing proof Step 4
(blueprint: lem-trf-support-product-base-change). -/
def supportProduct (f : U ⟶ B) (g : V ⟶ B) (p : T ⟶ U) (q : T ⟶ V)
    (h : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left) :
    (spLower (l := l) (E := E) (n := n) (p ≫ f)).obj
        (spUnit (l := l) (E := E) (n := n) T) ⟶
      (spLower (l := l) (E := E) (n := n) f).obj
          (spUnit (l := l) (E := E) (n := n) U) ⊗
        (spLower (l := l) (E := E) (n := n) g).obj
          (spUnit (l := l) (E := E) (n := n) V) :=
  (supportComp (F := F) (l := l) (E := E) (n := n) p f
      (supportCompactification p)
      (supportCompactification f)
      (supportCompactification (p ≫ f))).inv.app
      (spUnitLoc (l := l) (E := E) (n := n) T) ≫
    (spLower (l := l) (E := E) (n := n) f).map
      ((spLower (l := l) (E := E) (n := n) p).map (unitPull (l := l) (E := E) (n := n) q).inv ≫
        (supportExchange (F := F) (l := l) (E := E) (n := n)
          (a := q.hom.left) (v := f.hom.left) h.flip
          (supportCompactification g)
          (supportCompactification p)).inv.app
            (spUnitLoc (l := l) (E := E) (n := n) V)) ≫
    (@asIso _ _ _ _ (projectionUnitMap f (supportCtf (l := l) (E := E) (n := n) g).obj)
      (projectionUnit_isIso (F := F) (l := l) (E := E) (n := n) f
        (supportCtf (l := l) (E := E) (n := n) g))).inv ≫
    ((spLower (l := l) (E := E) (n := n) f).map
      (coefficientUnitIso l E n U.obj.left).inv ▷ _)

/-- `χ`: inverse composition along `q,g`, after the equality `fp=gq` of the square.
Source: Step 4, inverse compact-support composition
(blueprint: lem-trf-support-product-base-change). -/
def otherComposition (f : U ⟶ B) (g : V ⟶ B) (p : T ⟶ U) (q : T ⟶ V)
    (h : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left) :
    (spLower (l := l) (E := E) (n := n) (p ≫ f)).obj
        (spUnit (l := l) (E := E) (n := n) T) ⟶
      (spLower (l := l) (E := E) (n := n) g).obj
        ((spLower (l := l) (E := E) (n := n) q).obj
          (spUnit (l := l) (E := E) (n := n) T)) :=
  eqToHom (congrArg (fun r : T ⟶ B ↦
      (spLower (l := l) (E := E) (n := n) r).obj
        (spUnit (l := l) (E := E) (n := n) T))
      (ObjectProperty.hom_ext _ (f := p ≫ f) (g := q ≫ g) (Over.OverMorphism.ext h.w))) ≫
    (supportComp (F := F) (l := l) (E := E) (n := n) q g
      (supportCompactification q)
      (supportCompactification g)
      (supportCompactification (q ≫ g))).inv.app
        (spUnitLoc (l := l) (E := E) (n := n) T)

/-- The other expression: `Rg_!((bc_AU)⁻¹) ∘ χ`, with `Lp^*A_U ≅ A_T`.
Source: Step 4, the displayed other-leg comparison
(blueprint: lem-trf-support-product-base-change). -/
def otherBaseChange (f : U ⟶ B) (g : V ⟶ B) (p : T ⟶ U) (q : T ⟶ V)
    (h : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left) :
    (spLower (l := l) (E := E) (n := n) (p ≫ f)).obj
        (spUnit (l := l) (E := E) (n := n) T) ⟶
      (spLower (l := l) (E := E) (n := n) g).obj
        ((pull l E n g.hom.left).obj
          ((spLower (l := l) (E := E) (n := n) f).obj
            (spUnit (l := l) (E := E) (n := n) U))) :=
  otherComposition (l := l) (E := E) (n := n) f g p q h ≫
    (spLower (l := l) (E := E) (n := n) g).map
      ((spLower (l := l) (E := E) (n := n) q).map (unitPull (l := l) (E := E) (n := n) p).inv ≫
        (supportExchange (F := F) (l := l) (E := E) (n := n)
          (a := p.hom.left) (v := g.hom.left) h
          (supportCompactification f)
          (supportCompactification q)).inv.app
            (spUnitLoc (l := l) (E := E) (n := n) U))

/-- The prescribed support-product arrow is an isomorphism.
Source: Step 4 and def-trf-supported-pairing Step 2
(blueprint: lem-trf-support-product-base-change).
Proof: inverse composition and exchange are isomorphisms on the localizing closure;
constant pullback and unit constraints are isomorphisms. The compactly supported constant
object is in Dctf, so the projection isomorphism applies. Compose these isomorphisms. -/
theorem supportProduct_isIso (f : U ⟶ B) (g : V ⟶ B) (p : T ⟶ U) (q : T ⟶ V)
    (h : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left) :
    IsIso (supportProduct (l := l) (E := E) (n := n) f g p q h) := by
  unfold supportProduct
  infer_instance

/-- The other-leg projection is an isomorphism on exactly the stated Dctf domain.
Source: Step 4, definition of `π_g(N)` (blueprint: lem-trf-support-product-base-change).
Proof: apply prop-functor-package (5) to the constant unit on V and N; compose with the
unit isomorphism and signed symmetry. No extra hypothesis on N is used. -/
theorem projectionOtherLeg_isIso (g : V ⟶ B) (N : Ctf l E n B.obj.left) :
    IsIso (projectionOtherLeg (l := l) (E := E) (n := n) g N.obj) := by
  let := braiding l E n B.obj.left
  let := projectionUnit_isIso (F := F) (l := l) (E := E) (n := n) g N
  unfold projectionOtherLeg
  infer_instance

/-- The support recipe agrees with base change along the other leg.
Source: latest blueprint diagonal-pairing proof Step 4
(blueprint: lem-trf-support-product-base-change).
Proof: (1) expand μ using inverse composition, inverse exchange along f, unit insertion,
and inverse projection formula, exactly as def-trf-supported-pairing Step 2.
(2) apply π_g to Rf_!A_U, using the signed symmetry and unit A_V; expand χ along q,g.
Naturality of projection formula transports the composite to the exchange along g.
(3) the composition, Cartesian exchange and projection-formula coherence equations of
prop-functor-package (3)--(5) identify the two composites, after Lp^*A_U ≅ A_T.
The inverse unit constraint occurs before inverse projection formula throughout. -/
theorem supportProduct_baseChange (f : U ⟶ B) (g : V ⟶ B) (p : T ⟶ U) (q : T ⟶ V)
    (h : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left) :
    supportProduct (l := l) (E := E) (n := n) f g p q h ≫
        projectionOtherLeg (l := l) (E := E) (n := n) g
          ((spLower (l := l) (E := E) (n := n) f).obj
            (spUnit (l := l) (E := E) (n := n) U)) =
      otherBaseChange (l := l) (E := E) (n := n) f g p q h := by
  sorry

end WeilConjectures.TrfSupportProduct
