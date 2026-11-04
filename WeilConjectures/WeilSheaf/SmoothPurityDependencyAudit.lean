/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData
import all WeilConjectures.CategoryTheory.Native.NativeWeilTensorConstraintLifts
import all WeilConjectures.WeilSheaf.AffineLineBundle
import all WeilConjectures.WeilSheaf.Bidual
import all WeilConjectures.WeilSheaf.BifunctorHomShift
import all WeilConjectures.WeilSheaf.BifunctorHomTriangulated
import all WeilConjectures.WeilSheaf.Category
import all WeilConjectures.WeilSheaf.Cohomology
import all WeilConjectures.WeilSheaf.CompactProjectionFormula
import all WeilConjectures.WeilSheaf.CondensedModelBaseChange
import all WeilConjectures.WeilSheaf.CondensedModelBaseChangeCoherence
import all WeilConjectures.WeilSheaf.CondensedModelBoundedConstructible
import all WeilConjectures.WeilSheaf.CondensedModelCompactSupport
import all WeilConjectures.WeilSheaf.CondensedModelDescent
import all WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback
import all WeilConjectures.WeilSheaf.CondensedModelWeil
import all WeilConjectures.WeilSheaf.CondensedModelWeilCoherence
import all WeilConjectures.WeilSheaf.CondensedModelWeilDerived
import all WeilConjectures.WeilSheaf.Constant
import all WeilConjectures.WeilSheaf.ConstantTwistCohomology
import all WeilConjectures.WeilSheaf.CurryIsoCriterion
import all WeilConjectures.WeilSheaf.Defs
import all WeilConjectures.WeilSheaf.DerivedHom
import all WeilConjectures.WeilSheaf.DerivedHomConstructible
import all WeilConjectures.WeilSheaf.DerivedHomPrecomposition
import all WeilConjectures.WeilSheaf.DerivedHomSingleResolution
import all WeilConjectures.WeilSheaf.DerivedHomTriangulated
import all WeilConjectures.WeilSheaf.DirectImageRestriction
import all WeilConjectures.WeilSheaf.DirectImageStalk
import all WeilConjectures.WeilSheaf.Dual
import all WeilConjectures.WeilSheaf.ExtensionByZeroAdjunction
import all WeilConjectures.WeilSheaf.ExtensionByZeroDerived
import all WeilConjectures.WeilSheaf.FiniteLeray
import all WeilConjectures.WeilSheaf.Fourier
import all WeilConjectures.WeilSheaf.FourierInversion.Defs
import all WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
import all WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist
import all WeilConjectures.WeilSheaf.FrobeniusDerived
import all WeilConjectures.WeilSheaf.GeometricFiberPullback
import all WeilConjectures.WeilSheaf.HomologySequence
import all WeilConjectures.WeilSheaf.HomologyShift
import all WeilConjectures.WeilSheaf.HomotopyInvariance
import all WeilConjectures.WeilSheaf.HomotopyInvariance.Basic
import all WeilConjectures.WeilSheaf.HomotopyInvariance.Lisse
import all WeilConjectures.WeilSheaf.HomotopyInvariance.Restriction
import all WeilConjectures.WeilSheaf.IhomCurry
import all WeilConjectures.WeilSheaf.IhomLisse.Comp
import all WeilConjectures.WeilSheaf.IhomLisse.CompWeil
import all WeilConjectures.WeilSheaf.IhomLisse.UpperStar
import all WeilConjectures.WeilSheaf.IhomLisse.UpperStarComparison
import all WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual
import all WeilConjectures.WeilSheaf.Isotypic
import all WeilConjectures.WeilSheaf.IsotypicPullback
import all WeilConjectures.WeilSheaf.LisseDuality
import all WeilConjectures.WeilSheaf.LisseLocus
import all WeilConjectures.WeilSheaf.Localization
import all WeilConjectures.WeilSheaf.LowerShriek
import all WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import all WeilConjectures.WeilSheaf.LowerShriekIndependence
import all WeilConjectures.WeilSheaf.LowerStar
import all WeilConjectures.WeilSheaf.LowerStarComp
import all WeilConjectures.WeilSheaf.LowerStarId
import all WeilConjectures.WeilSheaf.Native.NativeAdicRestrictionFlat
import all WeilConjectures.WeilSheaf.Native.NativeClosedTransposition
import all WeilConjectures.WeilSheaf.Native.NativeCoefficientTensorComparison
import all WeilConjectures.WeilSheaf.Native.NativeCoherentInverseHomSquare
import all WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
import all WeilConjectures.WeilSheaf.Native.NativeCompatibleTowerCalculation
import all WeilConjectures.WeilSheaf.Native.NativeDerivedWeilTensorConstructible
import all WeilConjectures.WeilSheaf.Native.NativeForgetNormalizedBinaryModels
import all WeilConjectures.WeilSheaf.Native.NativeFrobeniusCoherentRingedModel
import all WeilConjectures.WeilSheaf.Native.NativeFrobeniusRingedModel
import all WeilConjectures.WeilSheaf.Native.NativeGeometricHomComparison
import all WeilConjectures.WeilSheaf.Native.NativeGeometricTensorComparison
import all WeilConjectures.WeilSheaf.Native.NativeHomEvaluationSquareAllSources
import all WeilConjectures.WeilSheaf.Native.NativeHomRepresentativeExistence
import all WeilConjectures.WeilSheaf.Native.NativeHomRepresentativeUniqueness
import all WeilConjectures.WeilSheaf.Native.NativeImmersionHeartLocalization
import all WeilConjectures.WeilSheaf.Native.NativeNormalizedActionHom
import all WeilConjectures.WeilSheaf.Native.NativeNormalizedTensorModels
import all WeilConjectures.WeilSheaf.Native.NativeRestrictionForgetTotalModel
import all WeilConjectures.WeilSheaf.Native.NativeRingedForgetTensorChainComparison
import all WeilConjectures.WeilSheaf.Native.NativeStandardHomRepresentatives
import all WeilConjectures.WeilSheaf.Native.NativeTensorAcyclicTestComparison
import all WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatForget
import all WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatRepresentatives
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenDerivedTensor
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenProperInterchange
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenRestrictionTensor
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenSheafProjectionTensor
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenSheafTensorExistence
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorCanonicalData
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorExtensionDescent
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorForgetNormalization
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorFullKFlatLocalization
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorLocalization
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalization
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalizedRestrictionDescent
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorPresentationExistence
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorRestrictionForget
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorRestrictionForgetKFlat
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorSheafComparisons
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorUnitNormalization
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryBiduality
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryCanonicalTensorRepresentatives
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryClosedTensorModels
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryHomTransport
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryKFlatLocalization
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryOpenTensorSupport
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRepresentativeCurrying
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRestrictionTensor
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRestrictionTotalModel
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRingedTensorChainComparison
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRingedTensorUnderivedData
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorIdentification
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelNaturality
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelResolutionData
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelResolutionExtension
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelResolutionNaturality
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelResolutionRoof
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelResolutionTransport
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorRepresentatives
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilChainUncurryForget
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilHomClosedStructure
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilHomRightAdjoint
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRepresentativeCurrying
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRepresentativeUncurry
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRingedPresentation
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRingedTensorModel
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRowHomComparison
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnderivedTensor
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnitMateIsIso
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorAdjoints
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorChain
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorCoherence
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorEvaluation
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorForgetKFlat
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorGeometry
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorLift
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChain
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainAssembly
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainData
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainRingedSquare
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainTransport
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorComplexSquare
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorLocalizationSquare
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorModel
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorModelLeftSquare
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorModelRightSquare
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorModelSquares
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorNormalized
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorRepresentatives
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBinaryChainSquare
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBinaryModelComparison
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridge
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridgeData
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedChainData
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedChainLaws
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedComplexModel
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedComplexes
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquare
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquareNative
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquareNativeCoherence
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquareNativeComparison
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquareOrdinary
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedForgetBinary
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedForgetLocalization
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedKFlatData
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedKFlatFlat
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedKFlatLocalization
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedKFlatLocalizationEquivalence
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedKFlatResolution
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedLeftUnitRepresentatives
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModelNaturality
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedStructure
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapComplex
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapLocalization
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapModel
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapSummand
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTransport
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTripleComplex
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedBinarySquare
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedData
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedIso
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnitSymmetryRepresentatives
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorTransport
import all WeilConjectures.WeilSheaf.NativeFrobeniusRingedModel.NativeActionSiteHomComparison
import all WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
import all WeilConjectures.WeilSheaf.OpenImmersion
import all WeilConjectures.WeilSheaf.Operations
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryRelativeTensorIdentification
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorTermwiseComparison
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorTotalComparison
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorUnderivedNaturality
import all WeilConjectures.WeilSheaf.ProperBaseChange
import all WeilConjectures.WeilSheaf.ProperBaseChangeFunctor
import all WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek
import all WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion
import all WeilConjectures.WeilSheaf.ProperLowerStarAdjoint
import all WeilConjectures.WeilSheaf.ProperProjectionFormula
import all WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryRingedTensorCoherence
import all WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryTensorInverseAssociativity
import all WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
import all WeilConjectures.WeilSheaf.SixFunctors.UnderlyingStandardHomRepresentatives
import all WeilConjectures.WeilSheaf.SixFunctors.WeilGeometricHomConstructibility
import all WeilConjectures.WeilSheaf.SmoothBaseChange
import all WeilConjectures.WeilSheaf.SmoothPurity
import all WeilConjectures.WeilSheaf.SmoothPurityAbsoluteDescent
import all WeilConjectures.WeilSheaf.SmoothPurityAffineLineConstant
import all WeilConjectures.WeilSheaf.SmoothPurityBaseChangeNormalization
import all WeilConjectures.WeilSheaf.SmoothPurityCompactConstant
import all WeilConjectures.WeilSheaf.SmoothPurityCompactHomotopy
import all WeilConjectures.WeilSheaf.SmoothPurityCondensedCarrier
import all WeilConjectures.WeilSheaf.SmoothPurityCondensedTraceCriterion
import all WeilConjectures.WeilSheaf.SmoothPurityDerivedSquareComp
import all WeilConjectures.WeilSheaf.SmoothPurityDescendedProperUniversality
import all WeilConjectures.WeilSheaf.SmoothPurityDescendedWeilUniversality
import all WeilConjectures.WeilSheaf.SmoothPurityDescentNormalization
import all WeilConjectures.WeilSheaf.SmoothPurityDescentSingle
import all WeilConjectures.WeilSheaf.SmoothPurityDescentUnit
import all WeilConjectures.WeilSheaf.SmoothPurityFieldTrace
import all WeilConjectures.WeilSheaf.SmoothPurityFreeComparison
import all WeilConjectures.WeilSheaf.SmoothPurityFreeResolution
import all WeilConjectures.WeilSheaf.SmoothPurityNativeDescent
import all WeilConjectures.WeilSheaf.SmoothPurityNativeDescentPullback
import all WeilConjectures.WeilSheaf.SmoothPurityNativeDirectTraceCriterion
import all WeilConjectures.WeilSheaf.SmoothPurityNativeDualizingDescent
import all WeilConjectures.WeilSheaf.SmoothPurityNativeHomShift
import all WeilConjectures.WeilSheaf.SmoothPurityNativeHomSingle
import all WeilConjectures.WeilSheaf.SmoothPurityNativeProperDualizing
import all WeilConjectures.WeilSheaf.SmoothPurityNativeProperTrace
import all WeilConjectures.WeilSheaf.SmoothPurityNativeTensorTate
import all WeilConjectures.WeilSheaf.SmoothPurityNativeTensorTateShift
import all WeilConjectures.WeilSheaf.SmoothPurityProperPointTrace
import all WeilConjectures.WeilSheaf.SmoothPurityProperRelativeTrace
import all WeilConjectures.WeilSheaf.SmoothPurityProperTraceCoordinates
import all WeilConjectures.WeilSheaf.SmoothPuritySeparatedAdjunction
import all WeilConjectures.WeilSheaf.SmoothPurityThom
import all WeilConjectures.WeilSheaf.SmoothPurityThomDescent
import all WeilConjectures.WeilSheaf.SmoothPurityTraceCriterion
import all WeilConjectures.WeilSheaf.SmoothPurityTraceDescent
import all WeilConjectures.WeilSheaf.SmoothPurityWhiskering
import all WeilConjectures.WeilSheaf.SplitTorsor
import all WeilConjectures.WeilSheaf.Stalk
import all WeilConjectures.WeilSheaf.StalkCharpoly
import all WeilConjectures.WeilSheaf.StalkConstantSheaf
import all WeilConjectures.WeilSheaf.StalkFrobenius
import all WeilConjectures.WeilSheaf.StalkFunctor
import all WeilConjectures.WeilSheaf.StalkIso
import all WeilConjectures.WeilSheaf.StalkMonoidal
import all WeilConjectures.WeilSheaf.StalkPairing
import all WeilConjectures.WeilSheaf.StalkTensor
import all WeilConjectures.WeilSheaf.StalkUpperStar
import all WeilConjectures.WeilSheaf.StrictWeilComplex
import all WeilConjectures.WeilSheaf.Supporting.CompletedCoefficientRingedCoherence
import all WeilConjectures.WeilSheaf.TateTwist
import all WeilConjectures.WeilSheaf.TateTwistCohomology
import all WeilConjectures.WeilSheaf.Tensor
import all WeilConjectures.WeilSheaf.TensorHomAdjunction
import all WeilConjectures.WeilSheaf.TorsorPairing
import all WeilConjectures.WeilSheaf.TraceFunctionCongr
import all WeilConjectures.WeilSheaf.TraceFunctionOps
import all WeilConjectures.WeilSheaf.Triangle
import all WeilConjectures.WeilSheaf.UnitForget
import all WeilConjectures.WeilSheaf.UpperShriek
import all WeilConjectures.WeilSheaf.UpperShriekGeometric
import all WeilConjectures.WeilSheaf.UpperStarComp
import all WeilConjectures.WeilSheaf.UpperStarConstant
import all WeilConjectures.WeilSheaf.UpperStarId
import all WeilConjectures.WeilSheaf.UpperStarLowerStar
import all WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
import all WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil
import all WeilConjectures.WeilSheaf.VerdierBiduality
import all WeilConjectures.WeilSheaf.VerdierDual
import all WeilConjectures.WeilSheaf.VerdierDualLocalization
import all WeilConjectures.WeilSheaf.VerdierDualUpperShriek
import all WeilConjectures.WeilSheaf.VerdierExchange
import all WeilConjectures.WeilSheaf.VerdierExchangeNatural
import Lean

/-! # Declaration dependency audit for the absolute-purity Thom route

This command reports the declarations containing a direct use of `sorryAx`
reachable from the final conditional Thom theorem. It creates no mathematical
declaration and does not participate in its proof.
-/

open Lean in
run_elab do
  let root :=
    `AlgebraicGeometry.WeilComplex.nonempty_trivialLineThom_of_tate_encoding
  let env ← getEnv
  logInfo m!"Root: {root}; axioms: {← collectAxioms root}"
  let mut pending := #[root]
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
      if info.isAxiom then
        unavailable := unavailable.push name
        continue
      let deps := info.type.getUsedConstants ++
        ((info.value? true).map Expr.getUsedConstants).getD #[]
      if deps.contains `sorryAx then
        leaves := leaves.push name
      else if deps.isEmpty then
        unavailable := unavailable.push name
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
    `AlgebraicGeometry.WeilComplex.nonempty_upperShriek_iso_of_smoothOfRelativeDimension,
    `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth,
    `AlgebraicGeometry.WeilComplex.exists_natTrans_upperShriek_isIso_forget_of_smooth]
  for name in forbidden do
    if seen.contains name then
      throwError "The Thom proof uses the relative-purity declaration {name}"
  unless unavailable.isEmpty do
    throwError "The dependency audit needs the imported proof bodies listed above"
