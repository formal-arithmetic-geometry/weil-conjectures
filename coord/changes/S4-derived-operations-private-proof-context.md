# DerivedPullbackTensorHom private proof context

## Reason

Six existing theorem proofs are completed without changing any public declaration
signature, definition, instance, existing docstring, or import. Generic private proved
helpers need additional universe names. The tensor comparison uses a local irreducibility
attribute inside its own section so Lean uses the stated object and Hom formulas rather
than unfolding selected functors. Its dependent transport calculation uses a scoped
heartbeat option; the complete file compiles within the unchanged 60-second limit.
Preflight treats these command changes as interface changes, so this record makes
their scope and unchanged consumer behavior explicit. No downstream file is edited.

## Old

```lean
universe u v
```

The existing scalar-comparison section had no nested tensor-proof section.

## New

After the existing definitions of rational operations, before the generic private helpers:

```lean
universe r s w x
```

Around only `rationalTensorScalarComparison_existsUnique`, following the proved
private integral-naturality lemma:

```lean
section
attribute [local irreducible] rationalDerivedTensor sfRationalScalarExtension

set_option maxHeartbeats 800000 in
-- The bilinear comparison's dependent object transports exceed the default heartbeat budget.
-- Existing docstring and unchanged theorem signature; completed proof.

end
```

Every added helper is private and proved. The local attribute ends before the existing
public definition `rationalTensorScalarComparison`. No attribute or instance is exported.
All 51 existing declaration signatures were compared verbatim with the shared source.
No target statement or definition used by a target changes its meaning.

## Users

The item and all transitive Lean importers are listed below, with current claim holders.
Every consumer keeps the same public signatures, data, imports, instances and meaning.
No consumer adaptation is needed. The dependency set agrees with the source import graph.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | Q3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | V1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | B7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | K9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | C5 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | U1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | U2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | D9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | K7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | B9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.AmbTateRootProjectionReduction | R4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | N3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ClopenRoosIntegralDescent | S8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CoefficientHeart | D6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | T8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CommonStageLocallyFree | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | C4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompletedPullbackTensorComparison | S1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CompletedTensorScalarLinearity | E7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.CondensedBoundedHomContinuity | S3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | X7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ConstantWeilStructure | F2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | F7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | X8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | T2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ConstructibleTruncations | X9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | F4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | W4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | G6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DerivedOpenSquareRestriction | C6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorHom | S4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorIso | A2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | W5 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.EffectiveComparisonRealizationModels | A3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | Y5 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | X2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.EtaleIsoDescent | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | G1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FdPullbackComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | R7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | Y6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | A4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Y7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | Y8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | F9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteOpenProductSwap | N3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteProductFieldCoefficientDescent | B2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteProjectionActionLaws | G2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteProperProductTranspose | N4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FinitePullbackTensorComparison | F8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteTateSiteDescent | T4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FourierAdicArtinSchreier | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | B3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IdentificationFibreAdjunction | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | W6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | S4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralBoundedStratumBaseChange | Y3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralCoherenceTower | M1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | K5 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralCompositionCounitImages | J3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | T3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | B5 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | T9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | P2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | W7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | G3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralLineReductionRestriction | J8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralModels | U1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | Y6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | A5 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralPullbackReductionCounit | B4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | K6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | G4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | J4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | P1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.InverseImagePullbackComparisonDerived | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonNatural | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | E9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IsomorphismScalarAugmentationCone | F7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IsomorphismScalarComparisonAgreement | D8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.IsomorphismScalarTensorKFlatModel | S6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.LatticeSubquotientFiltration | X3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | Z5 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | H1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.LocalizedDirectImageComparison | S2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | R4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | B8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | U4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.NormedCoefficientRealization | V3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PointAutomorphismRestrictionNatural | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PointAutomorphismTransportScalarExtension | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PointExactDerivedModel | H2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorBasic | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PointTransformationCoefficientDescent | C1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | H3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | D6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | M2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | D9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PurityFiniteKummerLevel | A9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PurityFiniteOpenIntervalDescent | H4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | G6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.QlbarDirectImageComparison | V4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.QuotientExpressionKFlatNormalization | G9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.QuotientSystemMixedCoherence | C2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | C3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | J8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | G7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | G2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.ScalarModelImmersionExtension | B5 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | P8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | A6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | Q6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SfWeilSheafComplex | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | E1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | K1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | K2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | H1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.StratifiedConstantModelProductBound | T4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | D2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | S3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.StrictQuotientExpressions | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | P5 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SupportedHomCocycleNormalization | H5 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SupportedHomPullback | B8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | V7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | Z6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | V9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.WeilComplexQbarIdempotentComplete | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | D3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | Y2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | E2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | E4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | A2 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | A6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | A7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | J1 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | Z9 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | K3 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | A7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | W4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | S4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | R6 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | W8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | A8 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.TraceFormula.IntegralComparisonCounitCharacterization | K4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | H7 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | D4 | Unchanged public interface and meaning; no adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Unchanged public interface and meaning; no adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Unchanged public interface and meaning; no adaptation. |

## Status

landed 20261021T175009-L-3961883 2026-10-21 (merge of deliver/S4/Sheaf.Paper.DerivedPullbackTensorHom)
