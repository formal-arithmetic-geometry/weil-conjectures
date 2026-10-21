# AlgebraicGeometry.Scheme.pbcAmbientScalarExtension_preserves

## Reason

Fill the eight remaining proof holes of `Sheaf.Paper.FiniteStagePairCategory`.
The new private proved helpers identify the completed coefficient maps, descend
natural transformations through scalar localization, and transport normalized
adjunction coherence. Private proof imports expose existing private proof lemmas
without adding any public dependency. Scoped transparency options, `omit`,
`include`, and a scoped removal of `ULift.module` only control elaboration of
these proofs. The three chosen comparison definitions are locally irreducible
from the rational cocycle proof onward, so coherence rewrites use their named
normalization equations rather than expanding nested chosen witnesses. Three
private unit lemmas unfold precisely the comparison they identify. These local
reducibility attributes expire at the end of the section and change no imported
interface or construction. The file-local tensor notation scope only affects
parsing in this module. The command scanner may conservatively classify these helper commands
as an interface change.

Every existing public signature, instance attribute, public import and
non-theorem body remains unchanged. No consumer requires adaptation. Target
statements and the meanings of their definitions therefore remain unchanged.

## Old

```lean
theorem pbcAmbientScalarExtension_preserves (h : E ≤ F)
    [IsNoetherian T] (_hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : pbcIntegralStage l Ω T E) :
    PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F)
      ((pbcAmbientScalarExtension l Ω T h).obj K.obj) := by
  sorry
```

## New

```lean
theorem pbcAmbientScalarExtension_preserves (h : E ≤ F)
    [IsNoetherian T] (_hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : pbcIntegralStage l Ω T E) :
    PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F)
      ((pbcAmbientScalarExtension l Ω T h).obj K.obj) := by
  change PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F)
    ((pbcDerivedExtend (pbcCompletedScalarMap l Ω T h)).obj K.obj)
  rw [pbcStageCoefficientMap_eq l Ω T h]
  exact pbcEmbeddingAmbientTensor_preserves l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T _hdim _hl K
```

The other seven theorem bodies and new private helpers are in the same module;
all retain the public signatures recorded in the shared source.

## Users

`tools/downstream.py Sheaf.Paper.FiniteStagePairCategory --uses
pbcRationalScalarExtension_exists` reports 358 transitive importers and finds
the declaration name only in the item module. The following conservative table
records every importer, with its current claim holder. None is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteStagePairCategory | H8 | Eight proof bodies and private helpers. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | Q3 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | V1 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | K9 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | D9 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent | Y2 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AmbTateRootProjectionReduction | R4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | P5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AmbientCompleteRawSystem | Q5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AutomorphismCompletionUnitComparison | E2 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCalculus | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompleteCompactSupportProetale | S3 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | F6 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedExchangeCoherence | S9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedPerfectScalarPullback | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedERealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | P7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteTateSiteDescent | T4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralLineReductionRestriction | J8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntrinsicQbarCategory | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | K9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | S4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | G5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcAutomorphismTransport | F3 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcCommonStageCones | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcConeIndependence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcDescentFunctors | J5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | A8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcFilteredRetractDescent | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcFiniteRawScalarComparison | S7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcIdempotentCompleteTriangulation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcPairFunctorShiftCoherence | A3 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcQbarCategory | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcQbarCompletedPullback | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcQbarIdempotentComplete | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcSupportCondition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcVerdierAxioms | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcWeilCategory | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PulledReductionStrictTowerComparison | M1 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityFiniteKummerLevel | A9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityFiniteOpenIntervalDescent | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | G6 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RealSheafSections | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RealizationCompletedPull | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | P8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfConstructibleCanonicalCompleteness | G2 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfExactPullbackCounitNormalization | G9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | P9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedHomCocycleNormalization | H5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedHomPullback | B8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilKernelHenselianInertia | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Public interface unchanged; no adaptation. |

## Status

landed 20261021T203616-L-3843420 2026-10-21 (merge of deliver/H8/Sheaf.Paper.FiniteStagePairCategory)
