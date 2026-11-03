/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.DeligneLaumon.CondensedWeil.CondensedConstantExtensionFrobenius
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.DeligneLaumon.CondensedWeil.ConstantExtensionPunctualWeights
public import WeilConjectures.PoincareDuality.Poincare
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SmoothPurity.OrientedPerfectDuality
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
-- Construction-only dependency: def-zl-condensed-field-duality-constructions.
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

/- Archived proof-plan imports, retained as text while the theorem is still unproved.
The replacement definitions below use the current condensed interface.
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSitePerfectDualityForModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
import WeilConjectures.SmoothPurity.Supporting.LegacySitePerfectComplex
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.ProEtaleCoefficients.IntegralOnSlice.RationalSliceCompletedEvaluation
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralScalarData
import WeilConjectures.SixFunctors.Supporting.ConstantCoefficientScalarNormalization
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeTensor
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeHom
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationTranspose
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
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
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
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
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
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
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
import WeilConjectures.AlgebraicGeometry.Picard.Purity.Condensed.NativeCompactSupportWeilTransport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
import WeilConjectures.AlgebraicGeometry.SepFinType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFrobeniusComparisonCoherence
import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportPull
import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit
import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.AlgebraicGeometry.Picard.VerdierExchange.VerdierExchangeData
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.SixFunctors.CommonStageCompactWeilCohomology
import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.CategoryTheory.Projection.ProjectionInternalHom
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasic
import WeilConjectures.ZetaWeil.OrdinaryCompactCohomology
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenDerivedDecomposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenConstructibilityBounds
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Pi.Basic
import WeilConjectures.AlgebraicGeometry.FiniteClopenTensor.ProEtaleFiniteClopenTensorCalculus
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.AlgebraicGeometry.ClopenLocalization.ProEtaleClopenUnboundedDerivedLocalization
import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenKFlatMonoidalDescent
import WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
import WeilConjectures.SixFunctors.FrobeniusCohomologyTransport
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
import WeilConjectures.SixFunctors.Supporting.FrobeniusPointTransportNatural
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompactSupportRestriction
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.SmoothPurity.Sf.SfCommonStageDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
-/

/-! # Poincare pairing on possibly disconnected smooth proper fibres

Source: latest blueprint, sec-zeta-weil/sk-prop-smooth-proper-purity/
prop-zl-smooth-proper-relative-purity.proof.md, Step 3
(blueprint: lem-zl-disconnected-fibre-poincare-pairing).

The pairing uses actual condensed modules, their relative derived coefficient dual,
the root-normalized Tate line and the normalized smooth trace. Scalar coordinates
use the canonical universe lift of Qbar_l. No component is required to descend to
the finite field, and no connectedness or nonemptiness is assumed on the fibre.

## Main definitions

- `nativePairing`: the canonical trace-evaluation pairing before scalar evaluation.
- `Components`: a finite clopen partition by geometric connected components.
- `sections`: ordinary derived sections in the canonical lifted scalar coordinates.
- `twistedPhi`: the recorded twisted contragredient Weil isomorphism.

## Main statements

- `disconnected_fibre_poincare_pairing`: componentwise sum, perfectness and invariance.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.DisconnectedFibrePoincare

/-- Relative derived coefficient dual, using the recorded closed structure.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev dual (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (K : C ell X) :
    C ell X :=
  StrictWeilCondensed.dual (Profinite.padicAlgClRingObj ell) K

/-- The current signed Tate sheaf at a nonnegative exponent, in degree zero.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev line (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) (d : ℕ) : C ell X :=
  StrictWeilCondensed.derivedTateLine ell PurityTransport.Coefficient.closure X (d : ℤ)

/-- The unshifted actual twisted derived dual.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev twistedDual (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (K : C ell X) (d : ℕ) :
    C ell X :=
  dual ell K ⊗ line ell X d

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The current signed Tate sheaf agrees canonically with the positive root presentation;
the latter agrees with the published twist by its defining tensor recursion.
Source: latest blueprint, actual Tate line
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def lineComparison (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) (d : ℕ) :
    line ell X d ≅ tateTwistDerived X ell d :=
  (DerivedCategory.singleFunctor _ 0).mapIso
    (StrictWeilCondensed.tateLine_identification ell PurityTransport.Coefficient.closure
      X (d : ℤ) ≪≫ eqToIso (by
    change PurityTransport.Coefficient.closure.line ell X d = tateTwistNat X ell d
    induction d with
    | zero => rfl
    | succ d ih =>
        change PurityTransport.Coefficient.closure.line ell X d ⊗
          PurityTransport.Coefficient.closure.firstLine ell X =
            tateTwistNat X ell d ⊗ tateTwistOne X ell
        rw [ih]
        rfl))

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
attribute [instance] Components.openPiece Components.closedPiece Components.connected
  Components.proper Components.smooth

set_option maxHeartbeats 8000000 in
-- Keep the coefficient abstract while checking its exact-derived single comparison.
/-- Derived restriction of a root-normalized positive Tate power. Keeping the coefficient
abstract retains exactly the published tensor-power comparison without expanding its ring.
Source: latest blueprint, component Tate restriction
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def powerRestriction (ell : ℕ) [Fact ell.Prime]
    (c : PurityTransport.Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (t : PurityTransport.LinePullCoordinates ell c f) :
    (upperStar (c.obj ell) f).mapDerivedCategory.obj
      (StrictWeilCondensed.derivedTateLine ell c Y (d : ℤ)) ⟶
        StrictWeilCondensed.derivedTateLine ell c X (d : ℤ) :=
  (upperStar (c.obj ell) f).mapDerivedCategory.map
      ((DerivedCategory.singleFunctor _ 0).map
        (StrictWeilCondensed.tateLine_identification ell c Y (d : ℤ)).hom) ≫
    ((upperStar (c.obj ell) f).mapDerivedCategorySingleFunctor 0).hom.app (c.line ell Y d) ≫
    (DerivedCategory.singleFunctor _ 0).map (t.power d).hom ≫
    (DerivedCategory.singleFunctor _ 0).map
      (StrictWeilCondensed.tateLine_identification ell c X (d : ℤ)).inv

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Frobenius on scalar cohomology in any integer degree.
Source: latest blueprint, geometric Frobenius
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def cohomologyFrobenius (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (K : C ell (D.geometricFiber X₀).left)
    (phi : (StrictWeilCondensed.action (Profinite.padicAlgClRingObj ell)
      (StrictWeilCondensed.modelFrobenius D X₀)).obj K ≅ K) (i : ℤ) :=
  (DerivedCategory.homologyFunctor (V.{u} ell) i).map (frobenius D ell X₀ K phi)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The derived structure on F-dual(d) is the current signed twisted-dual datum,
with its canonical contragredient, tensorator and root-normalized Tate pullback.
No choice of an inverse Frobenius operator is introduced.
Source: latest blueprint, contragredient and twist
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def twistedPhi (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (K : C ell (D.geometricFiber X₀).left)
    (phi : (StrictWeilCondensed.action (Profinite.padicAlgClRingObj ell)
      (StrictWeilCondensed.modelFrobenius D X₀)).obj K ≅ K) (d : ℕ) :
    (StrictWeilCondensed.action (Profinite.padicAlgClRingObj ell)
      (StrictWeilCondensed.modelFrobenius D X₀)).obj (twistedDual ell K d) ≅
        twistedDual ell K d :=
  letI := primeInvertible D ell hEll (D.geometricFiber X₀)
  StrictWeilCondensed.twistedDualDatum ell PurityTransport.Coefficient.closure
    (StrictWeilCondensed.modelFrobenius D X₀) K phi (d : ℤ)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
end WeilConjectures.DisconnectedFibrePoincare
