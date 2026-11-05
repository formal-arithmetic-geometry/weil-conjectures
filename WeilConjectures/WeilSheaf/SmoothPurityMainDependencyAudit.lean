/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all WeilConjectures.LeanEval.WeilConjectures
import all WeilConjectures.Statement
import all WeilConjectures.WeilSheaf.AffineLineBundle
import all WeilConjectures.WeilSheaf.AffineLineCohomology
import all WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
import all WeilConjectures.WeilSheaf.ArtinSchreierDual
import all WeilConjectures.WeilSheaf.ArtinSchreierFrobenius
import all WeilConjectures.WeilSheaf.ArtinSchreierFunctions
import all WeilConjectures.WeilSheaf.ArtinSchreierInertia
import all WeilConjectures.WeilSheaf.ArtinSchreierIsotypic
import all WeilConjectures.WeilSheaf.ArtinSchreierMul
import all WeilConjectures.WeilSheaf.ArtinSchreierMulGeometric
import all WeilConjectures.WeilSheaf.ArtinSchreierNeg
import all WeilConjectures.WeilSheaf.ArtinSchreierPlane
import all WeilConjectures.WeilSheaf.ArtinSchreierPullback
import all WeilConjectures.WeilSheaf.ArtinSchreierPurity
import all WeilConjectures.WeilSheaf.ArtinSchreierTrace
import all WeilConjectures.WeilSheaf.ArtinSchreierTrivialization
import all WeilConjectures.WeilSheaf.Bidual
import all WeilConjectures.WeilSheaf.BifunctorHomShift
import all WeilConjectures.WeilSheaf.BifunctorHomTriangulated
import all WeilConjectures.WeilSheaf.BoundaryStalk
import all WeilConjectures.WeilSheaf.Category
import all WeilConjectures.WeilSheaf.CohomologicalRange
import all WeilConjectures.WeilSheaf.CohomologicalRangeAffine
import all WeilConjectures.WeilSheaf.Cohomology
import all WeilConjectures.WeilSheaf.CohomologyAdicConstant
import all WeilConjectures.WeilSheaf.CohomologyAdicConstantExt
import all WeilConjectures.WeilSheaf.CohomologyAdicConstantLattice
import all WeilConjectures.WeilSheaf.CohomologyDegreeZero
import all WeilConjectures.WeilSheaf.CohomologyExact
import all WeilConjectures.WeilSheaf.CohomologyNonneg
import all WeilConjectures.WeilSheaf.CohomologyProEtale
import all WeilConjectures.WeilSheaf.CohomologyResolution
import all WeilConjectures.WeilSheaf.CohomologySequence
import all WeilConjectures.WeilSheaf.CohomologyShift
import all WeilConjectures.WeilSheaf.CohomologyZero
import all WeilConjectures.WeilSheaf.CompactProjectionFormula
import all WeilConjectures.WeilSheaf.CompactSupportAdicConstant
import all WeilConjectures.WeilSheaf.CondensedLisseRepresentation
import all WeilConjectures.WeilSheaf.CondensedModelBaseChange
import all WeilConjectures.WeilSheaf.CondensedModelBaseChangeCoherence
import all WeilConjectures.WeilSheaf.CondensedModelBoundedConstructible
import all WeilConjectures.WeilSheaf.CondensedModelCompactSupport
import all WeilConjectures.WeilSheaf.CondensedModelDescent
import all WeilConjectures.WeilSheaf.CondensedModelFiniteLevel
import all WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback
import all WeilConjectures.WeilSheaf.CondensedModelWeil
import all WeilConjectures.WeilSheaf.CondensedModelWeilCoherence
import all WeilConjectures.WeilSheaf.CondensedModelWeilDerived
import all WeilConjectures.WeilSheaf.CondensedTwistedConstant
import all WeilConjectures.WeilSheaf.Constant
import all WeilConjectures.WeilSheaf.ConstantFieldComponent
import all WeilConjectures.WeilSheaf.ConstantFieldEquivalence
import all WeilConjectures.WeilSheaf.ConstantFieldIrreducible
import all WeilConjectures.WeilSheaf.ConstantFieldPullback
import all WeilConjectures.WeilSheaf.ConstantFieldRestriction
import all WeilConjectures.WeilSheaf.ConstantGeometricFiberPullback
import all WeilConjectures.WeilSheaf.ConstantTwistCohomology
import all WeilConjectures.WeilSheaf.ConstantTwistCondensed
import all WeilConjectures.WeilSheaf.ConstantTwistWeight
import all WeilConjectures.WeilSheaf.CurryIsoCriterion
import all WeilConjectures.WeilSheaf.Curve
import all WeilConjectures.WeilSheaf.CurveEndpoints
import all WeilConjectures.WeilSheaf.CurvePullback
import all WeilConjectures.WeilSheaf.CurveTopCohomology
import all WeilConjectures.WeilSheaf.Defs
import all WeilConjectures.WeilSheaf.DenseOpen
import all WeilConjectures.WeilSheaf.DerivedHom
import all WeilConjectures.WeilSheaf.DerivedHomConstructible
import all WeilConjectures.WeilSheaf.DerivedHomPrecomposition
import all WeilConjectures.WeilSheaf.DerivedHomSingleResolution
import all WeilConjectures.WeilSheaf.DerivedHomTriangulated
import all WeilConjectures.WeilSheaf.DirectImageRestriction
import all WeilConjectures.WeilSheaf.DirectImageStalk
import all WeilConjectures.WeilSheaf.DirectImageStalkMap
import all WeilConjectures.WeilSheaf.Dual
import all WeilConjectures.WeilSheaf.DualIrreducible
import all WeilConjectures.WeilSheaf.EquivariantPullback
import all WeilConjectures.WeilSheaf.EquivariantPullbackExchange
import all WeilConjectures.WeilSheaf.EulerProduct
import all WeilConjectures.WeilSheaf.ExtensionByZeroAdjunction
import all WeilConjectures.WeilSheaf.ExtensionByZeroDerived
import all WeilConjectures.WeilSheaf.FieldCoefficient
import all WeilConjectures.WeilSheaf.FieldCoefficientCohomology
import all WeilConjectures.WeilSheaf.FieldCoefficientExtendScalars
import all WeilConjectures.WeilSheaf.FieldCoefficientTateTwist
import all WeilConjectures.WeilSheaf.FieldCoefficientTransition
import all WeilConjectures.WeilSheaf.FieldCoefficientTwoColimit
import all WeilConjectures.WeilSheaf.FiniteEtale
import all WeilConjectures.WeilSheaf.FiniteEtaleLisse
import all WeilConjectures.WeilSheaf.FiniteLength
import all WeilConjectures.WeilSheaf.FiniteLeray
import all WeilConjectures.WeilSheaf.FiniteLowerStar
import all WeilConjectures.WeilSheaf.Finiteness
import all WeilConjectures.WeilSheaf.Fourier
import all WeilConjectures.WeilSheaf.FourierInversion
import all WeilConjectures.WeilSheaf.FourierPlancherel
import all WeilConjectures.WeilSheaf.FourierStalk
import all WeilConjectures.WeilSheaf.FourierTateTwist
import all WeilConjectures.WeilSheaf.FourierTrace
import all WeilConjectures.WeilSheaf.FourierTraceAux
import all WeilConjectures.WeilSheaf.FrobeniusDerived
import all WeilConjectures.WeilSheaf.FrobeniusTwist
import all WeilConjectures.WeilSheaf.FrobeniusTwistStalk
import all WeilConjectures.WeilSheaf.FrobeniusTwistSubobject
import all WeilConjectures.WeilSheaf.GaloisGlobalSectionsTransport
import all WeilConjectures.WeilSheaf.GeometricCoinvariants
import all WeilConjectures.WeilSheaf.GeometricConstituent
import all WeilConjectures.WeilSheaf.GeometricFiberPullback
import all WeilConjectures.WeilSheaf.GeometricFiberPullbackTrace
import all WeilConjectures.WeilSheaf.GeometricFiberPullbackTraceFunction
import all WeilConjectures.WeilSheaf.GeometricallyConstant
import all WeilConjectures.WeilSheaf.GrothendieckLefschetz
import all WeilConjectures.WeilSheaf.HomologySequence
import all WeilConjectures.WeilSheaf.HomologyShift
import all WeilConjectures.WeilSheaf.HomotopyInvariance
import all WeilConjectures.WeilSheaf.IhomCurry
import all WeilConjectures.WeilSheaf.Isotypic
import all WeilConjectures.WeilSheaf.IsotypicPullback
import all WeilConjectures.WeilSheaf.LFunction
import all WeilConjectures.WeilSheaf.LSeries
import all WeilConjectures.WeilSheaf.LisseDuality
import all WeilConjectures.WeilSheaf.LisseFiltration
import all WeilConjectures.WeilSheaf.LisseLocus
import all WeilConjectures.WeilSheaf.LissePoincarePairing
import all WeilConjectures.WeilSheaf.LocalFrobenius
import all WeilConjectures.WeilSheaf.Localization
import all WeilConjectures.WeilSheaf.LowerShriek
import all WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import all WeilConjectures.WeilSheaf.LowerShriekIndependence
import all WeilConjectures.WeilSheaf.LowerShriekOperations
import all WeilConjectures.WeilSheaf.LowerShriekPackage
import all WeilConjectures.WeilSheaf.LowerStar
import all WeilConjectures.WeilSheaf.LowerStarComp
import all WeilConjectures.WeilSheaf.LowerStarId
import all WeilConjectures.WeilSheaf.LowerStarPairing
import all WeilConjectures.WeilSheaf.LowerStarTensorPow
import all WeilConjectures.WeilSheaf.LowerStarTriangulated
import all WeilConjectures.WeilSheaf.MiddleExtension
import all WeilConjectures.WeilSheaf.OpenClosedTriangle
import all WeilConjectures.WeilSheaf.OpenImmersion
import all WeilConjectures.WeilSheaf.OpenImmersionRestriction
import all WeilConjectures.WeilSheaf.Operations
import all WeilConjectures.WeilSheaf.PoincareDuality
import all WeilConjectures.WeilSheaf.PoincareDualityLisse
import all WeilConjectures.WeilSheaf.PoincareDualityLisseEquiv
import all WeilConjectures.WeilSheaf.PointTraceComparison
import all WeilConjectures.WeilSheaf.ProperBaseChange
import all WeilConjectures.WeilSheaf.ProperBaseChangeFunctor
import all WeilConjectures.WeilSheaf.ProperCohomology
import all WeilConjectures.WeilSheaf.ProperLowerStarAdjoint
import all WeilConjectures.WeilSheaf.ProperProjectionFormula
import all WeilConjectures.WeilSheaf.RealPurity
import all WeilConjectures.WeilSheaf.ShiftedSheaf
import all WeilConjectures.WeilSheaf.SmoothBaseChange
import all WeilConjectures.WeilSheaf.SmoothLisseOpen
import all WeilConjectures.WeilSheaf.SmoothPurity
import all WeilConjectures.WeilSheaf.SmoothPurityAbsolute
import all WeilConjectures.WeilSheaf.SmoothPurityAbsoluteDescent
import all WeilConjectures.WeilSheaf.SmoothPurityAffineLineConstant
import all WeilConjectures.WeilSheaf.SmoothPurityBaseChangeNormalization
import all WeilConjectures.WeilSheaf.SmoothPurityCanonicalTateScalar
import all WeilConjectures.WeilSheaf.SmoothPurityChangeCoefficientWeilLaw
import all WeilConjectures.WeilSheaf.SmoothPurityCoefficientDatumComp
import all WeilConjectures.WeilSheaf.SmoothPurityCoefficientFactor
import all WeilConjectures.WeilSheaf.SmoothPurityCompactConstant
import all WeilConjectures.WeilSheaf.SmoothPurityCompactHomotopy
import all WeilConjectures.WeilSheaf.SmoothPurityCondensedCarrier
import all WeilConjectures.WeilSheaf.SmoothPurityCondensedTraceCriterion
import all WeilConjectures.WeilSheaf.SmoothPurityConstantWeilDatum
import all WeilConjectures.WeilSheaf.SmoothPurityCyclotomicField
import all WeilConjectures.WeilSheaf.SmoothPurityCyclotomicScalar
import all WeilConjectures.WeilSheaf.SmoothPurityDerivedSquareComp
import all WeilConjectures.WeilSheaf.SmoothPurityDescendedProperUniversality
import all WeilConjectures.WeilSheaf.SmoothPurityDescendedWeilUniversality
import all WeilConjectures.WeilSheaf.SmoothPurityDescentNormalization
import all WeilConjectures.WeilSheaf.SmoothPurityDescentSingle
import all WeilConjectures.WeilSheaf.SmoothPurityDescentUnit
import all WeilConjectures.WeilSheaf.SmoothPurityFieldTrace
import all WeilConjectures.WeilSheaf.SmoothPurityFreeComparison
import all WeilConjectures.WeilSheaf.SmoothPurityFreeLevelComposition
import all WeilConjectures.WeilSheaf.SmoothPurityFreePullbackComp
import all WeilConjectures.WeilSheaf.SmoothPurityFreePullbackComposition
import all WeilConjectures.WeilSheaf.SmoothPurityFreePullbackCube
import all WeilConjectures.WeilSheaf.SmoothPurityFreeResolution
import all WeilConjectures.WeilSheaf.SmoothPurityFreeTowerCoefficientPullbackComp
import all WeilConjectures.WeilSheaf.SmoothPurityFreeTowerPullbackComp
import all WeilConjectures.WeilSheaf.SmoothPurityFrobeniusFactorAlias
import all WeilConjectures.WeilSheaf.SmoothPurityInverseSquare
import all WeilConjectures.WeilSheaf.SmoothPurityK4NativeScalarCoefficient
import all WeilConjectures.WeilSheaf.SmoothPurityK4NativeScalarEquation
import all WeilConjectures.WeilSheaf.SmoothPurityK4NativeScalarNamed
import all WeilConjectures.WeilSheaf.SmoothPurityK4NativeScalarRoot
import all WeilConjectures.WeilSheaf.SmoothPurityK4NativeScalarTransport
import all WeilConjectures.WeilSheaf.SmoothPurityLimitPullbackComposition
import all WeilConjectures.WeilSheaf.SmoothPurityMapModUnit
import all WeilConjectures.WeilSheaf.SmoothPurityNativeDescent
import all WeilConjectures.WeilSheaf.SmoothPurityNativeDescentPullback
import all WeilConjectures.WeilSheaf.SmoothPurityNativeDirectTraceCriterion
import all WeilConjectures.WeilSheaf.SmoothPurityNativeDualizingDescent
import all WeilConjectures.WeilSheaf.SmoothPurityNativeHomShift
import all WeilConjectures.WeilSheaf.SmoothPurityNativeHomSingle
import all WeilConjectures.WeilSheaf.SmoothPurityNativeProperDualizing
import all WeilConjectures.WeilSheaf.SmoothPurityNativeProperTrace
import all WeilConjectures.WeilSheaf.SmoothPurityNativeTateDescent
import all WeilConjectures.WeilSheaf.SmoothPurityNativeTensorTate
import all WeilConjectures.WeilSheaf.SmoothPurityNativeTensorTateShift
import all WeilConjectures.WeilSheaf.SmoothPurityOrdinaryPullIsoComp
import all WeilConjectures.WeilSheaf.SmoothPurityPairTransport
import all WeilConjectures.WeilSheaf.SmoothPurityProperPointTrace
import all WeilConjectures.WeilSheaf.SmoothPurityProperRelativeTrace
import all WeilConjectures.WeilSheaf.SmoothPurityProperTraceCoordinates
import all WeilConjectures.WeilSheaf.SmoothPurityPullCoefficientComposition
import all WeilConjectures.WeilSheaf.SmoothPurityPullbackForgetFactor
import all WeilConjectures.WeilSheaf.SmoothPurityRationalRootLaw
import all WeilConjectures.WeilSheaf.SmoothPurityRationalTrivialization
import all WeilConjectures.WeilSheaf.SmoothPurityRootFrobeniusLaw
import all WeilConjectures.WeilSheaf.SmoothPurityRootFrobeniusUnitLaw
import all WeilConjectures.WeilSheaf.SmoothPurityRootsNaturality
import all WeilConjectures.WeilSheaf.SmoothPurityScalarCoefficientTransport
import all WeilConjectures.WeilSheaf.SmoothPurityScalarComparison
import all WeilConjectures.WeilSheaf.SmoothPurityScalarCompositionNormalization
import all WeilConjectures.WeilSheaf.SmoothPurityScalarDatumConjugation
import all WeilConjectures.WeilSheaf.SmoothPurityScalarDatumNamed
import all WeilConjectures.WeilSheaf.SmoothPurityScalarFactorSquare
import all WeilConjectures.WeilSheaf.SmoothPurityScalarIsoTransport
import all WeilConjectures.WeilSheaf.SmoothPurityScalarPullback
import all WeilConjectures.WeilSheaf.SmoothPurityScalarPullbackInterface
import all WeilConjectures.WeilSheaf.SmoothPurityScalarSquare
import all WeilConjectures.WeilSheaf.SmoothPurityScalarWeilLaw
import all WeilConjectures.WeilSheaf.SmoothPuritySeparatedAdjunction
import all WeilConjectures.WeilSheaf.SmoothPurityTateCoefficientComposition
import all WeilConjectures.WeilSheaf.SmoothPurityTateCondensedEncoding
import all WeilConjectures.WeilSheaf.SmoothPurityTateDescentPair
import all WeilConjectures.WeilSheaf.SmoothPurityTateInterfacePair
import all WeilConjectures.WeilSheaf.SmoothPurityTateOnePair
import all WeilConjectures.WeilSheaf.SmoothPurityTatePowersComposition
import all WeilConjectures.WeilSheaf.SmoothPurityTatePowersDescentLaw
import all WeilConjectures.WeilSheaf.SmoothPurityTatePowersFactor
import all WeilConjectures.WeilSheaf.SmoothPurityTatePullbackComp
import all WeilConjectures.WeilSheaf.SmoothPurityTatePullbackFactor
import all WeilConjectures.WeilSheaf.SmoothPurityTatePullbackInterface
import all WeilConjectures.WeilSheaf.SmoothPurityTateTowerProjection
import all WeilConjectures.WeilSheaf.SmoothPurityTensorComposition
import all WeilConjectures.WeilSheaf.SmoothPurityThom
import all WeilConjectures.WeilSheaf.SmoothPurityThomDescent
import all WeilConjectures.WeilSheaf.SmoothPurityThomFromTate
import all WeilConjectures.WeilSheaf.SmoothPurityTraceCriterion
import all WeilConjectures.WeilSheaf.SmoothPurityTraceDescent
import all WeilConjectures.WeilSheaf.SmoothPurityUnitConstraint
import all WeilConjectures.WeilSheaf.SmoothPurityUnitDatumTransport
import all WeilConjectures.WeilSheaf.SmoothPurityWhiskerComponent
import all WeilConjectures.WeilSheaf.SmoothPurityWhiskering
import all WeilConjectures.WeilSheaf.SplitTorsor
import all WeilConjectures.WeilSheaf.Stalk
import all WeilConjectures.WeilSheaf.StalkAtPurity
import all WeilConjectures.WeilSheaf.StalkCharpoly
import all WeilConjectures.WeilSheaf.StalkComparison
import all WeilConjectures.WeilSheaf.StalkConstantSheaf
import all WeilConjectures.WeilSheaf.StalkConstantTwist
import all WeilConjectures.WeilSheaf.StalkExact
import all WeilConjectures.WeilSheaf.StalkExtensionByZero
import all WeilConjectures.WeilSheaf.StalkFrobenius
import all WeilConjectures.WeilSheaf.StalkFrobeniusPow
import all WeilConjectures.WeilSheaf.StalkFunctor
import all WeilConjectures.WeilSheaf.StalkInternalHom
import all WeilConjectures.WeilSheaf.StalkIso
import all WeilConjectures.WeilSheaf.StalkMonoidal
import all WeilConjectures.WeilSheaf.StalkPairing
import all WeilConjectures.WeilSheaf.StalkRationalPoint
import all WeilConjectures.WeilSheaf.StalkTensor
import all WeilConjectures.WeilSheaf.StalkTensorTrace
import all WeilConjectures.WeilSheaf.StalkTransportGeneral
import all WeilConjectures.WeilSheaf.StalkUpperStar
import all WeilConjectures.WeilSheaf.StalkUpperStarCharpoly
import all WeilConjectures.WeilSheaf.StrictWeilComplex
import all WeilConjectures.WeilSheaf.SupportSubobject
import all WeilConjectures.WeilSheaf.SupportUpperStar
import all WeilConjectures.WeilSheaf.TateFrobeniusCokernel
import all WeilConjectures.WeilSheaf.TateFrobeniusLevel
import all WeilConjectures.WeilSheaf.TateFrobeniusPullback
import all WeilConjectures.WeilSheaf.TateFrobeniusPullbackNaturality
import all WeilConjectures.WeilSheaf.TateFrobeniusTower
import all WeilConjectures.WeilSheaf.TateFrobeniusTrivialization
import all WeilConjectures.WeilSheaf.TateTwist
import all WeilConjectures.WeilSheaf.TateTwistCohomology
import all WeilConjectures.WeilSheaf.TateTwistCondensedBridge
import all WeilConjectures.WeilSheaf.TateTwistNativeTensor
import all WeilConjectures.WeilSheaf.Tensor
import all WeilConjectures.WeilSheaf.TensorHomAdjunction
import all WeilConjectures.WeilSheaf.TensorObjPairing
import all WeilConjectures.WeilSheaf.TensorPower
import all WeilConjectures.WeilSheaf.TorsorPairing
import all WeilConjectures.WeilSheaf.TraceCupAdicConstant
import all WeilConjectures.WeilSheaf.TraceFunction
import all WeilConjectures.WeilSheaf.TraceFunctionCongr
import all WeilConjectures.WeilSheaf.TraceFunctionOps
import all WeilConjectures.WeilSheaf.TraceFunctionTensor
import all WeilConjectures.WeilSheaf.TraceFunctionVanishing
import all WeilConjectures.WeilSheaf.TraceIsomorphism
import all WeilConjectures.WeilSheaf.TraceSeries
import all WeilConjectures.WeilSheaf.TraceTriangleAdditivity
import all WeilConjectures.WeilSheaf.Triangle
import all WeilConjectures.WeilSheaf.UnitForget
import all WeilConjectures.WeilSheaf.UpperShriek
import all WeilConjectures.WeilSheaf.UpperShriekGeometric
import all WeilConjectures.WeilSheaf.UpperShriekUnitTensorMap
import all WeilConjectures.WeilSheaf.UpperStarComp
import all WeilConjectures.WeilSheaf.UpperStarConstant
import all WeilConjectures.WeilSheaf.UpperStarExact
import all WeilConjectures.WeilSheaf.UpperStarFiniteEtale
import all WeilConjectures.WeilSheaf.UpperStarId
import all WeilConjectures.WeilSheaf.UpperStarLowerStar
import all WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
import all WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil
import all WeilConjectures.WeilSheaf.UpperStarPointwise
import all WeilConjectures.WeilSheaf.VerdierBiduality
import all WeilConjectures.WeilSheaf.VerdierDual
import all WeilConjectures.WeilSheaf.VerdierDualFinite
import all WeilConjectures.WeilSheaf.VerdierDualLocalization
import all WeilConjectures.WeilSheaf.VerdierDualUpperShriek
import all WeilConjectures.WeilSheaf.VerdierExchange
import all WeilConjectures.WeilSheaf.VerdierExchangeNatural
import all WeilConjectures.WeilSheaf.WeilDescent
import all WeilConjectures.WeilSheaf.WeilDescentConstantField
import all WeilConjectures.WeilSheaf.WeilDescentGeometricallyConnected
import all WeilConjectures.WeilSheaf.WeilDescentPullbackRepresentation
import all WeilConjectures.WeilSheaf.WeilDescentRepresentation
import all WeilConjectures.WeilSheaf.WeilGroupArithmetic
import all WeilConjectures.WeilSheaf.WeilMonodromy
import all WeilConjectures.WeilSheaf.WeilMonodromyGeneral
import all WeilConjectures.ZetaFunction.BettiNumbers
import all WeilConjectures.ZetaFunction.BettiSymmetry
import all WeilConjectures.ZetaFunction.CohomologicalFamily
import all WeilConjectures.ZetaFunction.CurveFactorDegree
import all WeilConjectures.ZetaFunction.CurveZeta
import all WeilConjectures.ZetaFunction.HasseWeil
import all WeilConjectures.ZetaFunction.IntegralFrobeniusFactors
import all WeilConjectures.ZetaFunction.Rationality
import all WeilConjectures.ZetaFunction.SmoothProper
import all WeilConjectures.ZetaFunction.TraceFormula
import all WeilConjectures.ZetaFunction.Weights
import all WeilConjectures.ZetaFunction.WeilFactorization
import all WeilConjectures.ZetaFunction.WeilObjectComparison
import all WeilConjectures.ZetaFunction.WeilObjectComparisonDevissage
import all WeilConjectures.ZetaFunction.WeilObjectComparisonLocal
import all WeilConjectures.ZetaFunction.WeilObjectComparisonOpenClosed
import all WeilConjectures.ZetaFunction.WeilObjectComparisonPullback
import all WeilConjectures.ZetaFunction.WeilObjectOfLisse
import all WeilConjectures.ZetaFunction.WeilObjectOfLisseCohomology
import all WeilConjectures.ZetaFunction.WeilObjectOfLisseGlobal
import all WeilConjectures.ZetaFunction.WeilObjectOfLisseLocal
import all WeilConjectures.ZetaFunction.WeilObjectOfLisseLocalGalois
import all WeilConjectures.ZetaFunction.WeilObjectOfLisseSpecTrace
import all WeilConjectures.ZetaFunction.WeilObjectOfLisseTraceFunction
import all WeilConjectures.ZetaFunction.WeilSheafObjectComparison
import all WeilConjectures.ZetaFunction.WeilSheafObjectComparisonInduction
import all WeilConjectures.ZetaFunction.WeilSheafObjectComparisonLisse
import all WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData
import all WeilConjectures.CategoryTheory.Native.NativeWeilTensorConstraintLifts
import all WeilConjectures.DeligneLaumon.Reduction.DirectImage
import all WeilConjectures.WeilSheaf.FourierInversion.OtherSections
import all WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
import all WeilConjectures.WeilSheaf.Native.NativeDerivedWeilTensorConstructible
import all WeilConjectures.WeilSheaf.Native.NativeForgetNormalizedBinaryModels
import all WeilConjectures.WeilSheaf.Native.NativeGeometricTensorComparison
import all WeilConjectures.WeilSheaf.Native.NativeNormalizedTensorModels
import all WeilConjectures.WeilSheaf.Native.NativeRestrictionForgetTotalModel
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenDerivedTensor
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorExtensionDescent
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorForgetNormalization
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorLocalization
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalization
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalizedRestrictionDescent
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorPresentationExistence
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorRestrictionForget
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorRestrictionForgetKFlat
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorUnitNormalization
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryOpenTensorSupport
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRestrictionTensor
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRestrictionTotalModel
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRingedTensorModel
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnitMateIsIso
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorAdjoints
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorCoherence
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorGeometry
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorLift
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquare
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquareNative
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquareNativeCoherence
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapLocalization
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTransport
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnitSymmetryRepresentatives
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorTransport
import all WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
import all WeilConjectures.CategoryTheory.K.KFlatBifunctorTensorHom
import all WeilConjectures.CategoryTheory.Normalized.NormalizedKFlatTensorModels
import all WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationCoherence
import all WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
import all WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationProjection
import all WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationSheafTensor
import all WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationTensorModels
import all WeilConjectures.WeilSheaf.Native.NativePullTensor
import all WeilConjectures.WeilSheaf.Native.NativeTensorAcyclicTestComparison
import all WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatRepresentatives
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenSheafProjectionTensor
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorCanonicalData
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorFullKFlatLocalization
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorSheafComparisons
import all WeilConjectures.WeilSheaf.Native.Projection.AdicSheafTensorSquare
import all WeilConjectures.WeilSheaf.Native.Projection.DerivedModelNormalizations
import all WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromModelFamilies
import all WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromModels
import all WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromTotalFunctors
import all WeilConjectures.WeilSheaf.Native.Projection.ModelSquareCancellation
import all WeilConjectures.WeilSheaf.Native.Projection.NativeComplexSquareNormalization
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedCoherenceOfSquare
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromCanonicalComparison
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromGeometricFunctor
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromNativeComparisons
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromNativeModels
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromNativeRestriction
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromOrdinaryComparison
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareOfRepresentatives
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedTensorSquare
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedTensorSquareOfTotal
import all WeilConjectures.WeilSheaf.Native.Projection.NativeModelFamilyNormalization
import all WeilConjectures.WeilSheaf.Native.Projection.NativeModelNormalization
import all WeilConjectures.WeilSheaf.Native.Projection.NativePullTensorNormalization
import all WeilConjectures.WeilSheaf.Native.Projection.NativeSheafTensorCore
import all WeilConjectures.WeilSheaf.Native.Projection.NativeSheafTensorSquare
import all WeilConjectures.WeilSheaf.Native.Projection.NativeTotalTensorCore
import all WeilConjectures.WeilSheaf.Native.Projection.NativeTotalTensorSquare
import all WeilConjectures.WeilSheaf.Native.Projection.NativeTotalTensorSquareOfSheaf
import all WeilConjectures.WeilSheaf.Native.Projection.ProperProjectionIso
import all WeilConjectures.WeilSheaf.Native.Projection.SheafTensorUnit
import all WeilConjectures.WeilSheaf.Native.Projection.TensorSquareCompatibility
import all WeilConjectures.WeilSheaf.Native.Projection.TotalSquareToModel
import all WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper
import all WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual
import all WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform
import all WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights
import all WeilConjectures.DeligneLaumon.AffineLine.Concentration
import all WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist
import all WeilConjectures.DeligneLaumon.AffineLine.Constituent
import all WeilConjectures.DeligneLaumon.AffineLine.Defs
import all WeilConjectures.DeligneLaumon.AffineLine.DegreeOne
import all WeilConjectures.DeligneLaumon.AffineLine.DenseOpen
import all WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit
import all WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional
import all WeilConjectures.DeligneLaumon.AffineLine.Exactness
import all WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents
import all WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary
import all WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude
import all WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport
import all WeilConjectures.DeligneLaumon.AffineLine.FourierWeight
import all WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul
import all WeilConjectures.DeligneLaumon.AffineLine.LaurentPoints
import all WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters
import all WeilConjectures.DeligneLaumon.AffineLine.LocalDuality
import all WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension
import all WeilConjectures.DeligneLaumon.AffineLine.Perverse
import all WeilConjectures.DeligneLaumon.AffineLine.Punctual
import all WeilConjectures.DeligneLaumon.AffineLine.PunctualSupport
import all WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform
import all WeilConjectures.DeligneLaumon.AffineLine.Purity
import all WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity
import all WeilConjectures.DeligneLaumon.AffineLine.RealPushforward
import all WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel
import all WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy
import all WeilConjectures.DeligneLaumon.AffineLine.Upper
import all WeilConjectures.DeligneLaumon.AffineLine.UpperReduction
import all WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension
import all WeilConjectures.DeligneLaumon.CommonStagePullbackCompComponent
import all WeilConjectures.DeligneLaumon.CommonStagePullbackCompData
import all WeilConjectures.DeligneLaumon.PrincipalIntrinsicCompletion.PrincipalIntrinsicCompletion
import all WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import all WeilConjectures.DeligneLaumon.QuotientTensorScalarTowerComparison
import all WeilConjectures.DeligneLaumon.Reduction.AffineCurve
import all WeilConjectures.DeligneLaumon.Reduction.CompactSupport
import all WeilConjectures.DeligneLaumon.Reduction.CurveTesting
import all WeilConjectures.DeligneLaumon.Reduction.FibreCohomology
import all WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage
import all WeilConjectures.DeligneLaumon.Reduction.FiniteEtaleChart
import all WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension
import all WeilConjectures.DeligneLaumon.Reduction.FormalSteps
import all WeilConjectures.DeligneLaumon.Reduction.MixedStalk
import all WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed
import all WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk
import all WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing
import all WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights
import all WeilConjectures.DeligneLaumon.Reduction.RealCurve
import all WeilConjectures.DeligneLaumon.Reduction.RealCurveConstituent
import all WeilConjectures.DeligneLaumon.Reduction.RealLissePurity
import all WeilConjectures.DeligneLaumon.Reduction.RealSheaves
import all WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine
import all WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep
import all WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification
import all WeilConjectures.DeligneLaumon.Reduction.TraceReality
import all WeilConjectures.DeligneLaumon.Reduction.Weights
import all WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import Lean

/-! # Declaration closure of the Weil conjectures after absolute purity

The audit reports all remaining sorry leaves, including leaves assigned to other workers.
Unavailable proof bodies are an error, so the reported closure is never silently incomplete.
-/

open Lean in
run_elab do
  let roots := #[
    `AlgebraicGeometry.Scheme.weil_conjectures,
    `LeanEval.AlgebraicGeometry.WeilConjectures.weil_conjectures]
  let env ← getEnv
  for root in roots do
    logInfo m!"Root: {root}; axioms: {← collectAxioms root}"
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut leaves : Array Name := #[]
  let mut unavailable : Array Name := #[]
  let mut inspected : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    unless (← collectAxioms name).contains `sorryAx do
      continue
    if let some idx := env.getModuleIdxFor? name then
      inspected := inspected.insert env.header.moduleNames[idx.toNat]!
    match env.checked.get.find? name with
    | none => unavailable := unavailable.push name
    | some info =>
      let deps ← match info with
        | .defnInfo v => pure (v.type.getUsedConstants ++ v.value.getUsedConstants)
        | .thmInfo v => pure (v.type.getUsedConstants ++ v.value.getUsedConstants)
        | .opaqueInfo v => pure (v.type.getUsedConstants ++ v.value.getUsedConstants)
        | .ctorInfo v => pure v.type.getUsedConstants
        | .recInfo v => pure v.type.getUsedConstants
        | .inductInfo v => pure (v.type.getUsedConstants ++ v.ctors.toArray)
        | .quotInfo _ => pure #[]
        | .axiomInfo _ =>
          unavailable := unavailable.push name
          pure #[]
      if deps.contains `sorryAx then
        leaves := leaves.push name
      else
        pending := pending ++ deps
  logInfo m!"Direct sorry dependencies: {leaves.qsort Name.lt}"
  logInfo m!"Unavailable dependency bodies: {unavailable.qsort Name.lt}"
  logInfo m!"Visited declarations: {seen.toArray.size}"
  let mut modules : NameSet := {}
  for name in unavailable do
    if let some idx := env.getModuleIdxFor? name then
      modules := modules.insert env.header.moduleNames[idx.toNat]!
  for name in modules.toArray.qsort Name.lt do
    logInfo m!"Missing import all: {name}"
  for name in inspected.toArray.qsort Name.lt do
    logInfo m!"Proof import all: {name}"
  let forbidden := #[
    `AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso,
    `AlgebraicGeometry.WeilComplex.nonempty_upperShriek_iso_of_smoothOfRelativeDimension,
    `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth,
    `AlgebraicGeometry.WeilComplex.exists_natTrans_upperShriek_isIso_forget_of_smooth]
  for name in forbidden do
    if seen.contains name && (← collectAxioms name).contains `sorryAx then
      throwError "The main theorem uses a relative-purity declaration with sorry: {name}"
  unless unavailable.isEmpty do
    throwError "The dependency audit needs the imported proof bodies listed above"
