/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
import WeilConjectures.FourierTransform.FourierSetting
import WeilConjectures.CategoryTheory.Adjunction.CondensedSixOperationPreservation
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Data.Finset.Max
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalBounded
import WeilConjectures.CategoryTheory.SixFunctors.CohomologicalSolutionSetRepresentability
import WeilConjectures.CategoryTheory.SixFunctors.SetGeneratedDerivedSolutionSet
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
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
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.CategoryTheory.ObjectProperty.Duality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedVerdierCoefficientComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.AlgebraicGeometry.FiniteCondensedVerdierComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullback
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
import WeilConjectures.CategoryTheory.RingObjects.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedVerdierScalarTransport
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.Internal.InternalFirstResidueRingIsoSupplement
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Embedded.EmbeddedIntegralCompletenessTransport
import WeilConjectures.SixFunctors.ProEtale.InternalCompletionStacksComparison
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentObjects
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentHom
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.AlgebraicGeometry.Derived.DerivedNakayamaFirstReduction
import WeilConjectures.AlgebraicGeometry.PrincipalTensorScalarExtension
import Mathlib.Algebra.Homology.Double
import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Shift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import Mathlib.Topology.Defs.Filter
import Mathlib.CategoryTheory.Monoidal.Mod
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
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
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRationalPushforward
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompCompositionBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedLocalization
import WeilConjectures.AlgebraicGeometry.Picard.IntrinsicSitePerfectHomWindow
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
import WeilConjectures.SixFunctors.Finite.FiniteConstructibleHom
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowDerivedSmoothBaseChange
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.Sf.SfBidualityClass
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
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
import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionStatement
import WeilConjectures.AlgebraicGeometry.Sf.SfCbcCompactSupportCompositionLimit
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import Mathlib.GroupTheory.OrderOfElement
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import Mathlib.Data.Nat.Prime.Infinite
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionZeroCompletion
import WeilConjectures.AlgebraicGeometry.Constant.ConstantOpenRestrictionModelComparison
import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationSheafExact
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientGeneralPullbackIso
import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
import Mathlib.CategoryTheory.Monoidal.CommMon_
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
import WeilConjectures.ProEtaleCoefficients.BoundedConstructibleCounterexample.NonFiniteMultiplicationKernel
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.SheafTensor
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import Mathlib.Algebra.Field.ZMod
import WeilConjectures.FourierTransform.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekShift
import WeilConjectures.CategoryTheory.Monoidal.SubcategoryShift
import WeilConjectures.PoincareDuality.ProjectionFormula
import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFourierKernelBounded

/-! # Composition of `ℚ̄_ℓ`-coefficient kernel transforms

The `ℚ̄_ℓ` case of the composition isomorphism used by lem-fd-inversion (node
lem-fd-kernel-composition-qbar): `condensedKernelCompositionIso_padicAlgCl`, the
kernel-composition isomorphism for bounded constructible kernels with coefficients in `ℚ̄_ℓ`,
and its Fourier specialization `KernelComposition.fourierCompositionIso_padicAlgCl`, with the
bounded constructibility of the Fourier kernel proved
(`KernelComposition.fourierKernel_padicAlgCl_boundedConstructible`). Only what the first
sentence of lem-fd-inversion's proof uses is stated; this is not the whole unit
lem-fd-kernel-composition at `ℚ̄_ℓ` (the convolution's membership in `D^b_c` and the restriction
of the transforms to `D^b_c` are not stated).
The proof is the unit's own route carried out at `Λ = ℚ̄_ℓ`, the direct twin of the `E`
construction (`Sheaf.Paper.CondensedKernelCompositionE`): compact-support base change along `q₁`,
projection formula for `r₂₃`, composition `q₂ ∘ r₂₃ = r₃`, projection formula for `r₁₃`,
`s₂ ∘ r₁₃ = r₃`, independence of the compactification and the shift `a + b`, all with the
`ℚ̄_ℓ`-coefficient six-functor isomorphisms of the interface.
Consumer: lem-fd-inversion at `Λ = ℚ̄_ℓ`.

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-fourier-transform/
sec-fourier-inversion/sk-thm-inversion/lem-fd-inversion.proof.md, first sentence, at
`Λ = ℚ̄_ℓ`; route of lem-fd-kernel-composition.proof.md
(blueprint: lem-fd-kernel-composition-qbar, from lem-fd-inversion).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Private copies of the private pasting and geometry helpers of
-- `Sheaf.Paper.CondensedKernelCompositionE` (private declarations are not imported).
-- The formal pasting uses only the displayed natural isomorphisms.
private def kernelCompositionPasting
    {A B C D₁₂ D₂₃ D₁₃ D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D₁₂] [Category* D₂₃]
    [Category* D₁₃] [Category* D]
    [MonoidalCategory D₁₂] [MonoidalCategory D₂₃] [MonoidalCategory D₁₃]
    [MonoidalCategory D]
    (P : A ⥤ D₁₂) (Q : B ⥤ D₂₃) (S : A ⥤ D₁₃)
    (Rp : D₁₂ ⥤ B) (Rq : D₂₃ ⥤ C) (Rs : D₁₃ ⥤ C)
    (U₁₂ : D₁₂ ⥤ D) (U₂₃ : D₂₃ ⥤ D) (U₁₃ : D₁₃ ⥤ D)
    (R₂₃ : D ⥤ D₂₃) (R₁₃ : D ⥤ D₁₃) (K : D₁₂) (L : D₂₃)
    (bc : Rp ⋙ Q ≅ U₁₂ ⋙ R₂₃)
    (tp : tensorRight K ⋙ U₁₂ ≅ U₁₂ ⋙ tensorRight (U₁₂.obj K))
    (pf₂₃ : R₂₃ ⋙ tensorRight L ≅ tensorRight (U₂₃.obj L) ⋙ R₂₃)
    (pc : P ⋙ U₁₂ ≅ S ⋙ U₁₃) (rc : R₂₃ ⋙ Rq ≅ R₁₃ ⋙ Rs)
    (pf₁₃ : U₁₃ ⋙ tensorRight (U₁₂.obj K ⊗ U₂₃.obj L) ⋙ R₁₃ ≅
      tensorRight (R₁₃.obj (U₁₂.obj K ⊗ U₂₃.obj L))) :
    (P ⋙ tensorRight K ⋙ Rp) ⋙ (Q ⋙ tensorRight L ⋙ Rq) ≅
      S ⋙ tensorRight (R₁₃.obj (U₁₂.obj K ⊗ U₂₃.obj L)) ⋙ Rs :=
  Functor.isoWhiskerLeft (P ⋙ tensorRight K)
      (Functor.isoWhiskerRight bc (tensorRight L ⋙ Rq)) ≪≫
    Functor.isoWhiskerLeft P
      (Functor.isoWhiskerRight tp (R₂₃ ⋙ tensorRight L ⋙ Rq)) ≪≫
    Functor.isoWhiskerLeft (P ⋙ U₁₂ ⋙ tensorRight (U₁₂.obj K))
      (Functor.isoWhiskerRight pf₂₃ Rq) ≪≫
    Functor.isoWhiskerLeft (P ⋙ U₁₂ ⋙ tensorRight (U₁₂.obj K) ⋙
      tensorRight (U₂₃.obj L)) rc ≪≫
    Functor.isoWhiskerLeft (P ⋙ U₁₂)
      (Functor.isoWhiskerRight (tensorRightTensor _ _).symm (R₁₃ ⋙ Rs)) ≪≫
    Functor.isoWhiskerRight pc
      (tensorRight (U₁₂.obj K ⊗ U₂₃.obj L) ⋙ R₁₃ ⋙ Rs) ≪≫
    Functor.isoWhiskerLeft S (Functor.isoWhiskerRight pf₁₃ Rs)

section Geometry

variable {k : Type u} [Field k] {B X Y : Over (Spec (.of k))}

private instance kernelMorphismFiniteType [LocallyOfFiniteType X.hom] (f : X ⟶ Y) :
    LocallyOfFiniteType f.left := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  exact locallyOfFiniteType_of_comp f.left Y.hom

private instance kernelMorphismSeparated [IsSeparated X.hom] (f : X ⟶ Y) :
    IsSeparated f.left := by
  have : IsSeparated (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  exact IsSeparated.of_comp f.left Y.hom

private instance kernelMorphismQuasiCompact [QuasiCompact X.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) : QuasiCompact f.left := by
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  exact QuasiCompact.of_comp f.left Y.hom

private abbrev kernelPair (f : X ⟶ B) (g : Y ⟶ B) : Over (Spec (.of k)) :=
  Over.mk (pullback.fst f.left g.left ≫ X.hom)

private abbrev kernelFst (f : X ⟶ B) (g : Y ⟶ B) : kernelPair f g ⟶ X :=
  Over.homMk (pullback.fst f.left g.left) rfl

private abbrev kernelSnd (f : X ⟶ B) (g : Y ⟶ B) : kernelPair f g ⟶ Y :=
  Over.homMk (pullback.snd f.left g.left) (by
    dsimp
    rw [← f.w, ← g.w, ← Category.assoc, ← Category.assoc, pullback.condition])

private instance kernelPairFiniteType [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ B) (g : Y ⟶ B) :
    LocallyOfFiniteType (kernelPair f g).hom := by
  change LocallyOfFiniteType (pullback.fst f.left g.left ≫ X.hom)
  infer_instance

private instance kernelPairQuasiCompact [QuasiCompact X.hom] [QuasiCompact Y.hom]
    [IsSeparated B.hom] (f : X ⟶ B) (g : Y ⟶ B) :
    QuasiCompact (kernelPair f g).hom := by
  change QuasiCompact (pullback.fst f.left g.left ≫ X.hom)
  infer_instance

private instance kernelPairSeparated [IsSeparated X.hom] [IsSeparated Y.hom]
    (f : X ⟶ B) (g : Y ⟶ B) : IsSeparated (kernelPair f g).hom := by
  change IsSeparated (pullback.fst f.left g.left ≫ X.hom)
  infer_instance

end Geometry

/-! ### The coefficient `ℚ̄_ℓ` (node lem-fd-kernel-composition-qbar)

The same calculation as for `E` (`Sheaf.Paper.CondensedKernelCompositionE`), with
the `ℚ̄_ℓ`-coefficient compact-support base change,
projection formula, composition and independence of the compactification. -/

section CalculationPadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X₁ X₂ X₃ X₁₂ X₂₃ X₁₃ T : Over (Spec (.of k))}
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType X₁₂.hom] [QuasiCompact X₁₂.hom] [IsSeparated X₁₂.hom]
  [LocallyOfFiniteType X₂₃.hom] [QuasiCompact X₂₃.hom] [IsSeparated X₂₃.hom]
  [LocallyOfFiniteType X₁₃.hom] [QuasiCompact X₁₃.hom] [IsSeparated X₁₃.hom]
  [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]

set_option hygiene false in
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
set_option hygiene false in
local notation "U" => boundedConstructibleUpperStar Λ ℓ
set_option hygiene false in
local notation "R" => boundedConstructibleLowerShriek ℓ
set_option hygiene false in
local notation "BC(" X ")" => BoundedConstructible (condensedRingObj Λ (X).left)

private def kernelInclusionCompatibilityPadicAlgCl
    (f : X₁₂ ⟶ X₁) (g : X₁₂ ⟶ X₂) (c : Compactification g.left)
    (K : BC(X₁₂)) (a : ℤ) :
    (U f ⋙ tensorRight K ⋙
      boundedConstructibleLowerShriekOfCompactification ℓ c ⋙
        shiftFunctor _ a) ⋙ (boundedConstructible (condensedRingObj Λ X₂.left)).ι ≅
    (boundedConstructible (condensedRingObj Λ X₁.left)).ι ⋙
      (upperStar Λ f.left).leftDerivedFunctor ⋙ tensorRight K.obj ⋙
        rightDerivedLowerShriekOfCompactification Λ c ⋙ shiftFunctor _ a := by
  exact Functor.isoWhiskerLeft
      (U f ⋙ tensorRight K ⋙ boundedConstructibleLowerShriekOfCompactification ℓ c)
      (((boundedConstructible (condensedRingObj Λ X₂.left)).ι).commShiftIso a) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (U f ⋙ tensorRight K)
          (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c) ≪≫
        Functor.isoWhiskerLeft (U f)
          (Functor.isoWhiskerRight
            ((boundedConstructible (condensedRingObj Λ X₁₂.left)).tensorRightCompιIso K)
            (rightDerivedLowerShriekOfCompactification Λ c)) ≪≫
        Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility Λ ℓ f)
          (tensorRight K.obj ⋙ rightDerivedLowerShriekOfCompactification Λ c)) _

set_option maxHeartbeats 8000000 in
-- The tensor and compact-support functors carry large coefficient-dependent instances.
set_option synthInstance.maxHeartbeats 8000 in
set_option synthInstance.maxSize 4096 in
private def kernelCompositionCalculationPadicAlgCl
    (p₁ : X₁₂ ⟶ X₁) (p₂ : X₁₂ ⟶ X₂)
    (q₁ : X₂₃ ⟶ X₂) (q₂ : X₂₃ ⟶ X₃)
    (s₁ : X₁₃ ⟶ X₁) (s₂ : X₁₃ ⟶ X₃)
    (r₁₂ : T ⟶ X₁₂) (r₂₃ : T ⟶ X₂₃) (r₁₃ : T ⟶ X₁₃)
    (sq : IsPullback r₁₂ r₂₃ p₂ q₁)
    (h₁ : r₁₂ ≫ p₁ = r₁₃ ≫ s₁) (h₃ : r₂₃ ≫ q₂ = r₁₃ ≫ s₂)
    (K : BC(X₁₂)) (L : BC(X₂₃)) :
    (U p₁ ⋙ tensorRight K ⋙ R p₂) ⋙ (U q₁ ⋙ tensorRight L ⋙ R q₂) ≅
      U s₁ ⋙ tensorRight ((R r₁₃).obj ((U r₁₂).obj K ⊗ (U r₂₃).obj L)) ⋙ R s₂ := by
  letI : BraidedCategory BC(T) :=
    letI := DerivedCategory.braidedCategory'
      (Mod (Sheaf (Scheme.ProEt.topology T.left) Ab.{u + 1}) (condensedRingObj Λ T.left))
    ObjectProperty.fullBraidedSubcategory _
  letI : BraidedCategory BC(X₁₃) :=
    letI := DerivedCategory.braidedCategory'
      (Mod (Sheaf (Scheme.ProEt.topology X₁₃.left) Ab.{u + 1}) (condensedRingObj Λ X₁₃.left))
    ObjectProperty.fullBraidedSubcategory _
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  let bc := asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
  let tp := (Functor.Monoidal.commTensorRight (U r₁₂) K).symm
  let pf₂₃ : R r₂₃ ⋙ tensorRight L ≅ tensorRight ((U r₂₃).obj L) ⋙ R r₂₃ :=
    NatIso.ofComponents
      (fun A ↦ asIso (boundedConstructibleExceptionalProjectionMorphism ℓ r₂₃ A L))
      (fun f ↦ boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ r₂₃ f L)
  let H := (U r₁₂).obj K ⊗ (U r₂₃).obj L
  let pf₁₃ : tensorLeft ((R r₁₃).obj H) ≅ U r₁₃ ⋙ tensorLeft H ⋙ R r₁₃ :=
    NatIso.ofComponents
      (fun A ↦ asIso (boundedConstructibleExceptionalProjectionMorphism ℓ r₁₃ H A))
      (fun f ↦ boundedConstructibleExceptionalProjectionMorphism_natural_right ℓ r₁₃ H f)
  let pc : U p₁ ⋙ U r₁₂ ≅ U s₁ ⋙ U r₁₃ :=
    (boundedConstructibleUpperStarComp Λ ℓ r₁₂ p₁).symm ≪≫
      eqToIso (congrArg (fun f ↦ U f) h₁) ≪≫ boundedConstructibleUpperStarComp Λ ℓ r₁₃ s₁
  let rc : R r₂₃ ⋙ R q₂ ≅ R r₁₃ ⋙ R s₂ :=
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r₂₃ q₂).symm ≪≫
      eqToIso (congrArg (fun f ↦ R f) h₃) ≪≫ boundedConstructibleLowerShriekComp_padicAlgCl ℓ r₁₃ s₂
  let pf : U r₁₃ ⋙ tensorRight H ⋙ R r₁₃ ≅ tensorRight ((R r₁₃).obj H) :=
    Functor.isoWhiskerLeft (U r₁₃)
        (Functor.isoWhiskerRight (BraidedCategory.tensorLeftIsoTensorRight H).symm (R r₁₃)) ≪≫
      pf₁₃.symm ≪≫ BraidedCategory.tensorLeftIsoTensorRight ((R r₁₃).obj H)
  exact kernelCompositionPasting (U p₁) (U q₁) (U s₁) (R p₂) (R q₂) (R s₂)
    (U r₁₂) (U r₂₃) (U r₁₃) (R r₂₃) (R r₁₃) K L bc tp pf₂₃ pc rc pf

set_option maxHeartbeats 1600000 in
-- The four compactification comparisons contain large coefficient-dependent instances.
set_option synthInstance.maxSize 4096 in
private def kernelCompositionCompactificationsPadicAlgCl
    (p₁ : X₁₂ ⟶ X₁) (p₂ : X₁₂ ⟶ X₂)
    (q₁ : X₂₃ ⟶ X₂) (q₂ : X₂₃ ⟶ X₃)
    (s₁ : X₁₃ ⟶ X₁) (s₂ : X₁₃ ⟶ X₃)
    (r₁₂ : T ⟶ X₁₂) (r₂₃ : T ⟶ X₂₃) (r₁₃ : T ⟶ X₁₃)
    (sq : IsPullback r₁₂ r₂₃ p₂ q₁)
    (h₁ : r₁₂ ≫ p₁ = r₁₃ ≫ s₁) (h₃ : r₂₃ ≫ q₂ = r₁₃ ≫ s₂)
    (c₁₂ : Compactification p₂.left) (c₂₃ : Compactification q₂.left)
    (c₁₃ : Compactification s₂.left) (cconv : Compactification r₁₃.left)
    (K : BC(X₁₂)) (L : BC(X₂₃)) (a b : ℤ) :
    let R₁₂ := boundedConstructibleLowerShriekOfCompactification ℓ c₁₂
    let R₂₃ := boundedConstructibleLowerShriekOfCompactification ℓ c₂₃
    let R₁₃ := boundedConstructibleLowerShriekOfCompactification ℓ c₁₃
    let Rc := boundedConstructibleLowerShriekOfCompactification ℓ cconv
    (U p₁ ⋙ tensorRight K ⋙ R₁₂ ⋙ shiftFunctor _ a) ⋙
        (U q₁ ⋙ tensorRight L ⋙ R₂₃ ⋙ shiftFunctor _ b) ≅
      U s₁ ⋙ tensorRight (Rc.obj ((U r₁₂).obj K ⊗ (U r₂₃).obj L)) ⋙
        R₁₃ ⋙ shiftFunctor _ (a + b) := by
  dsimp only
  let R₁₂ := boundedConstructibleLowerShriekOfCompactification ℓ c₁₂
  let R₂₃ := boundedConstructibleLowerShriekOfCompactification ℓ c₂₃
  let R₁₃ := boundedConstructibleLowerShriekOfCompactification ℓ c₁₃
  let Rc := boundedConstructibleLowerShriekOfCompactification ℓ cconv
  let H := (U r₁₂).obj K ⊗ (U r₂₃).obj L
  let e₁₂ : R₁₂ ≅ R p₂ :=
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₁₂
      (compactificationOverField p₂)
  let e₂₃ : R₂₃ ≅ R q₂ :=
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₂₃
      (compactificationOverField q₂)
  let e₁₃ : R₁₃ ≅ R s₂ :=
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₁₃
      (compactificationOverField s₂)
  let ec : Rc ≅ R r₁₃ :=
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ cconv
      (compactificationOverField r₁₃)
  let e : (U p₁ ⋙ tensorRight K ⋙ R₁₂) ⋙ (U q₁ ⋙ tensorRight L ⋙ R₂₃) ≅
      U s₁ ⋙ tensorRight (Rc.obj H) ⋙ R₁₃ :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (U p₁ ⋙ tensorRight K) e₁₂) _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft (U q₁ ⋙ tensorRight L) e₂₃) ≪≫
      kernelCompositionCalculationPadicAlgCl ℓ p₁ p₂ q₁ q₂ s₁ s₂ r₁₂ r₂₃ r₁₃ sq h₁ h₃ K L ≪≫
      Functor.isoWhiskerLeft (U s₁)
        (Functor.isoWhiskerRight ((curriedTensor BC(X₁₃)).flip.mapIso (ec.app H).symm) _ ≪≫
          Functor.isoWhiskerLeft _ e₁₃.symm)
  letI : (tensorRight L.obj).CommShift ℤ := DerivedCategory.commShiftTensorRight _ L.obj
  letI : (tensorRight L).CommShift ℤ := inferInstance
  letI : (rightDerivedLowerShriekOfCompactification Λ c₂₃).CommShift ℤ := by
    unfold rightDerivedLowerShriekOfCompactification
    infer_instance
  letI : R₂₃.CommShift ℤ := Functor.CommShift.ofComp
    (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c₂₃) ℤ
  let B := U q₁ ⋙ tensorRight L ⋙ R₂₃
  letI : B.CommShift ℤ := inferInstance
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (U p₁ ⋙ tensorRight K ⋙ R₁₂)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (B.commShiftIso a) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (shiftFunctorAdd _ a b).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _

end CalculationPadicAlgCl

/-- The kernel-composition isomorphism with coefficients in `ℚ̄_ℓ`, on the ambient transforms
restricted along the bounded constructible inclusion:
`ι ⋙ (Φ^a_𝒦 ⋙ Φ^b_{𝒦'}) ≅ ι ⋙ Φ^{a+b}_{𝒦' ∗ 𝒦}`. The construction of
`condensedKernelCompositionIso` with the `ℚ̄_ℓ`-coefficient compact-support base change,
projection formula, composition and independence of the compactification.
Consumer: lem-fd-inversion at `Λ = ℚ̄_ℓ`.
Source: lem-fd-inversion.proof.md, first sentence, at `Λ = ℚ̄_ℓ`; route of
lem-fd-kernel-composition.proof.md (blueprint: lem-fd-kernel-composition-qbar). -/
@[no_expose] def condensedKernelCompositionIso_padicAlgCl
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p] (hk : Finite k ∨ IsAlgClosed k)
    {S V V' V'' : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    [LocallyOfFiniteType V''.hom] [QuasiCompact V''.hom] [IsSeparated V''.hom]
    (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)
    (c₁₂ : Compactification (pullback.snd π.left π'.left))
    (c₂₃ : Compactification (pullback.snd π'.left π''.left))
    (c₁₃ : Compactification (pullback.snd π.left π''.left))
    (cconv : Compactification (pullback.tripleProj₁₃ π.left π'.left π''.left))
    (𝒦 : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ)
      (pullback π.left π'.left)))
    (𝒦' : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ)
      (pullback π'.left π''.left))) (a b : ℤ) :
    (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) V.left)).ι ⋙
        (condensedKernelTransform (Profinite.padicAlgClRingObj.{u} ℓ) π.left π'.left c₁₂
            𝒦.obj a ⋙
          condensedKernelTransform (Profinite.padicAlgClRingObj.{u} ℓ) π'.left π''.left c₂₃
            𝒦'.obj b) ≅
      (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) V.left)).ι ⋙
        condensedKernelTransform (Profinite.padicAlgClRingObj.{u} ℓ) π.left π''.left c₁₃
          (condensedKernelConvolution (Profinite.padicAlgClRingObj.{u} ℓ) π.left π'.left
            π''.left cconv 𝒦.obj 𝒦'.obj) (a + b) := by
  classical
  have _ := hk
  have : Fact (ringChar k).Prime := ⟨by simpa [ringChar.eq k p] using (Fact.out : p.Prime)⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by simpa [ringChar.eq k p] using hpℓ⟩
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let X₁₂ := kernelPair π π'
  let X₂₃ := kernelPair π' π''
  let X₁₃ := kernelPair π π''
  let p₁ : X₁₂ ⟶ V := kernelFst π π'
  let p₂ : X₁₂ ⟶ V' := kernelSnd π π'
  let q₁ : X₂₃ ⟶ V' := kernelFst π' π''
  let q₂ : X₂₃ ⟶ V'' := kernelSnd π' π''
  let s₁ : X₁₃ ⟶ V := kernelFst π π''
  let s₂ : X₁₃ ⟶ V'' := kernelSnd π π''
  let T := kernelPair p₂ q₁
  let r₁₂ : T ⟶ X₁₂ := kernelFst p₂ q₁
  let r₂₃ : T ⟶ X₂₃ := kernelSnd p₂ q₁
  let r₁₃ : T ⟶ X₁₃ := Over.homMk
    (pullback.tripleProj₁₃ π.left π'.left π''.left) (by
      dsimp [T, X₁₃, X₁₂, kernelPair, p₂, q₁]
      rw [← Category.assoc, pullback.tripleProj₁₃_fst, Category.assoc]
      rfl)
  have sq : IsPullback r₁₂ r₂₃ p₂ q₁ :=
    IsPullback.of_map_of_faithful (Over.forget _)
      (IsPullback.of_hasPullback p₂.left q₁.left)
  have h₁ : r₁₂ ≫ p₁ = r₁₃ ≫ s₁ := by
    apply Over.OverMorphism.ext
    exact (pullback.tripleProj₁₃_fst _ _ _).symm
  have h₃ : r₂₃ ≫ q₂ = r₁₃ ≫ s₂ := by
    apply Over.OverMorphism.ext
    exact (pullback.tripleProj₁₃_snd _ _ _).symm
  let U₁ := boundedConstructibleUpperStar Λ ℓ p₁
  let U₂ := boundedConstructibleUpperStar Λ ℓ q₁
  let U₃ := boundedConstructibleUpperStar Λ ℓ s₁
  let R₁ := boundedConstructibleLowerShriekOfCompactification (f := p₂) ℓ c₁₂
  let R₂ := boundedConstructibleLowerShriekOfCompactification (f := q₂) ℓ c₂₃
  let R₃ := boundedConstructibleLowerShriekOfCompactification (f := s₂) ℓ c₁₃
  let Rc := boundedConstructibleLowerShriekOfCompactification (f := r₁₃) ℓ cconv
  let H := (boundedConstructibleUpperStar Λ ℓ r₁₂).obj 𝒦 ⊗
    (boundedConstructibleUpperStar Λ ℓ r₂₃).obj 𝒦'
  let C := Rc.obj H
  let F₁₂ := U₁ ⋙ tensorRight 𝒦 ⋙ R₁ ⋙ shiftFunctor _ a
  let F₂₃ := U₂ ⋙ tensorRight 𝒦' ⋙ R₂ ⋙ shiftFunctor _ b
  let F₁₃ := U₃ ⋙ tensorRight C ⋙ R₃ ⋙ shiftFunctor _ (a + b)
  let ι₁ := (boundedConstructible (condensedRingObj Λ V.left)).ι
  let ι₂ := (boundedConstructible (condensedRingObj Λ V'.left)).ι
  let ι₃ := (boundedConstructible (condensedRingObj Λ V''.left)).ι
  let Φ₁₂ := condensedKernelTransform Λ π.left π'.left c₁₂ 𝒦.obj a
  let Φ₂₃ := condensedKernelTransform Λ π'.left π''.left c₂₃ 𝒦'.obj b
  let e₁₂ : F₁₂ ⋙ ι₂ ≅ ι₁ ⋙ Φ₁₂ := kernelInclusionCompatibilityPadicAlgCl ℓ p₁ p₂ c₁₂ 𝒦 a
  let e₂₃ : F₂₃ ⋙ ι₃ ≅ ι₂ ⋙ Φ₂₃ := kernelInclusionCompatibilityPadicAlgCl ℓ q₁ q₂ c₂₃ 𝒦' b
  let e₁₃ : F₁₃ ⋙ ι₃ ≅
      ι₁ ⋙ condensedKernelTransform Λ π.left π''.left c₁₃ C.obj (a + b) :=
    kernelInclusionCompatibilityPadicAlgCl ℓ s₁ s₂ c₁₃ C (a + b)
  let comp : F₁₂ ⋙ F₂₃ ≅ F₁₃ :=
    kernelCompositionCompactificationsPadicAlgCl ℓ p₁ p₂ q₁ q₂ s₁ s₂ r₁₂ r₂₃ r₁₃ sq h₁ h₃
      c₁₂ c₂₃ c₁₃ cconv 𝒦 𝒦' a b
  exact (Functor.associator ι₁ Φ₁₂ Φ₂₃).symm ≪≫
    Functor.isoWhiskerRight e₁₂.symm Φ₂₃ ≪≫
    Functor.associator F₁₂ ι₂ Φ₂₃ ≪≫
    Functor.isoWhiskerLeft F₁₂ e₂₃.symm ≪≫
    (Functor.associator F₁₂ F₂₃ ι₃).symm ≪≫
    Functor.isoWhiskerRight comp ι₃ ≪≫ e₁₃

namespace KernelComposition

/-- The prime `p` is a unit in the global sections of the condensed ring `ℚ̲̄_ℓ`
(`ℚ̄_ℓ` has characteristic `0`). -/
theorem isUnit_natCast_Γ_padicAlgClRingObj (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime] :
    IsUnit (p : MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) := by
  simpa only [map_natCast] using
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) :
      IsUnit (p : PadicAlgCl ℓ)).map (Profinite.PadicAlgCl.constRingHom.{u} ℓ)

/-- The Fourier kernel `K_ψ` in degree `0` on `X₁₂ = V ×_S V'`, at the coefficient `ℚ̄_ℓ`, with
the product structure over `k₀` induced from the base `S`, as in `condensedFourierTransform`.
Source: lem-fd-inversion.proof.md, first sentence (`FT_{ψ⁻¹} FT_ψ` as a kernel transform), at
`Λ = ℚ̄_ℓ` (blueprint: lem-fd-kernel-composition-qbar). -/
abbrev fourierKernel_padicAlgCl (ℓ : ℕ) [Fact ℓ.Prime]
    (k₀ : Type u) [Field k₀] [Fintype k₀] {S W W' : Over (Spec (.of k₀))}
    (ρ : W ⟶ S) (ρ' : W' ⟶ S)
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)))
    (b : Γ(pullback ρ.left ρ'.left, ⊤)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (pullback ρ.left ρ'.left)) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (pullback ρ.left ρ'.left))) :=
  letI : (pullback ρ.left ρ'.left).Over (Spec (.of k₀)) :=
    ⟨pullback.fst ρ.left ρ'.left ≫ ρ.left ≫ S.hom⟩
  (DerivedCategory.singleFunctor _ 0).obj
    (condensedFourierKernel (Profinite.padicAlgClRingObj.{u} ℓ) k₀ ρ.left ρ'.left ψ b)

/-- The Fourier kernel `fourierKernel_padicAlgCl` (coefficient `ℚ̄_ℓ`) is bounded constructible
(`condensedFourierKernel_boundedConstructible` at `k = k₀`, `p = char k₀ ≠ ℓ`).
Source: lem-fd-inversion.proof.md, first sentence (`FT_{ψ⁻¹} FT_ψ` as a kernel transform), at
`Λ = ℚ̄_ℓ` (blueprint: lem-fd-kernel-composition-qbar). -/
theorem fourierKernel_padicAlgCl_boundedConstructible (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    (hpℓ : p ≠ ℓ) (k₀ : Type u) [Field k₀] [Fintype k₀]
    {S W W' : Over (Spec (.of k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType W'.hom] [QuasiCompact W'.hom] [IsSeparated W'.hom]
    (ρ : W ⟶ S) (ρ' : W' ⟶ S)
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)))
    (b : Γ(pullback ρ.left ρ'.left, ⊤)) :
    boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (pullback ρ.left ρ'.left))
      (fourierKernel_padicAlgCl ℓ k₀ ρ ρ' ψ b) := by
  let : S.left.Over (Spec (.of k₀)) := ⟨S.hom⟩
  let : W.left.Over (Spec (.of k₀)) := ⟨W.hom⟩
  let : W'.left.Over (Spec (.of k₀)) := ⟨W'.hom⟩
  have : LocallyOfFiniteType (S.left ↘ Spec (.of k₀)) := ‹LocallyOfFiniteType S.hom›
  have : QuasiCompact (S.left ↘ Spec (.of k₀)) := ‹QuasiCompact S.hom›
  have : IsSeparated (S.left ↘ Spec (.of k₀)) := ‹IsSeparated S.hom›
  have : LocallyOfFiniteType (W.left ↘ Spec (.of k₀)) := ‹LocallyOfFiniteType W.hom›
  have : QuasiCompact (W.left ↘ Spec (.of k₀)) := ‹QuasiCompact W.hom›
  have : IsSeparated (W.left ↘ Spec (.of k₀)) := ‹IsSeparated W.hom›
  have : LocallyOfFiniteType (W'.left ↘ Spec (.of k₀)) := ‹LocallyOfFiniteType W'.hom›
  have : QuasiCompact (W'.left ↘ Spec (.of k₀)) := ‹QuasiCompact W'.hom›
  have : IsSeparated (W'.left ↘ Spec (.of k₀)) := ‹IsSeparated W'.hom›
  let : (pullback ρ.left ρ'.left).Over (Spec (.of k₀)) :=
    ⟨pullback.fst ρ.left ρ'.left ≫ ρ.left ≫ S.hom⟩
  exact condensedFourierKernel_boundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) p
    ⟨ℓ, inferInstance, hpℓ.symm, Or.inr (Or.inr ⟨Iso.refl _⟩)⟩
    (isUnit_natCast_Γ_padicAlgClRingObj ℓ p) k₀ (.inl inferInstance) k₀
    ρ.left ρ'.left ψ b

/-- `FT_φ ∘ FT_ψ ≅ Φ^{r+r}_{K_φ ∗ K_ψ}` on `D^b_c(V, ℚ̄_ℓ)`:
`condensedKernelCompositionIso_padicAlgCl` at the two Fourier kernels, over the finite field
`k₀` of characteristic `p ≠ ℓ`, the bounded constructibility of the kernels being
`fourierKernel_padicAlgCl_boundedConstructible`.
For lem-fd-inversion take `V' = V^∨`, `V'' = V`, `φ = ψ⁻¹` (resp. `ψ`) and the transposed pairing.
Source: lem-fd-inversion.proof.md, first sentence (`FT_{ψ⁻¹} FT_ψ` as a kernel transform), at
`Λ = ℚ̄_ℓ` (blueprint: lem-fd-kernel-composition-qbar). -/
def fourierCompositionIso_padicAlgCl (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    {S V V' V'' : Over (Spec (.of k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    [LocallyOfFiniteType V''.hom] [QuasiCompact V''.hom] [IsSeparated V''.hom]
    (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)
    (ψ φ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)))
    (b : Γ(pullback π.left π'.left, ⊤)) (b' : Γ(pullback π'.left π''.left, ⊤))
    (c₁₂ : Compactification (pullback.snd π.left π'.left))
    (c₂₃ : Compactification (pullback.snd π'.left π''.left))
    (c₁₃ : Compactification (pullback.snd π.left π''.left))
    (cconv : Compactification (pullback.tripleProj₁₃ π.left π'.left π''.left)) (r : ℤ) :
    letI : (pullback π.left π'.left).Over (Spec (.of k₀)) :=
      ⟨pullback.fst π.left π'.left ≫ π.left ≫ S.hom⟩
    letI : (pullback π'.left π''.left).Over (Spec (.of k₀)) :=
      ⟨pullback.fst π'.left π''.left ≫ π'.left ≫ S.hom⟩
    (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) V.left)).ι ⋙
        (condensedFourierTransform (Profinite.padicAlgClRingObj.{u} ℓ) k₀ π.left π'.left
            ψ b c₁₂ r ⋙
          condensedFourierTransform (Profinite.padicAlgClRingObj.{u} ℓ) k₀ π'.left π''.left
            φ b' c₂₃ r) ≅
      (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) V.left)).ι ⋙
        condensedKernelTransform (Profinite.padicAlgClRingObj.{u} ℓ) π.left π''.left c₁₃
          (condensedKernelConvolution (Profinite.padicAlgClRingObj.{u} ℓ) π.left π'.left
            π''.left cconv (fourierKernel_padicAlgCl ℓ k₀ π π' ψ b)
            (fourierKernel_padicAlgCl ℓ k₀ π' π'' φ b')) (r + r) :=
  condensedKernelCompositionIso_padicAlgCl p ℓ hpℓ k₀ (.inl inferInstance) π π' π''
    c₁₂ c₂₃ c₁₃ cconv
    ⟨_, fourierKernel_padicAlgCl_boundedConstructible p ℓ hpℓ k₀ π π' ψ b⟩
    ⟨_, fourierKernel_padicAlgCl_boundedConstructible p ℓ hpℓ k₀ π' π'' φ b'⟩ r r

end KernelComposition

end AlgebraicGeometry.ProEtale.CondensedRing
