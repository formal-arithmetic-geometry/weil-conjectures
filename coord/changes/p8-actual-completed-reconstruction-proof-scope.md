# AlgebraicGeometry.Scheme.pbc_actual_completed_reduction_reconstruction

## Reason

Preflight classifies added module commands as an interface change. The additions
are a temporary `ScalarComputation` section with local coefficient variables,
file-local elaboration options, and explicitly `[local irreducible]` attributes
for the normalized coefficient comparisons and scalar adjunctions. They keep
Lean from unfolding expensive chosen constructions during proof checking.
The section is closed before the public theorem. Every helper is private.
No existing definition, statement, attribute or public import is changed.
The public theorem's signature is byte-identical, as checked against the source.
These commands do not change any target's mathematical meaning and no target
statement review is reopened. This record documents the conservative static
classification; there is no forced consumer adaptation.

## Old

```lean
theorem pbc_actual_completed_reduction_reconstruction
    [HasCountableProducts (PbcCompletedDerived T d)]
    (K : PbcCompletedDerived T d) (hK : PbcIsIntrinsicallyComplete T d K) :
    let M : ℕᵒᵖ ⥤ PbcCompletedDerived T d :=
    Functor.ofOpSequence
        (X := fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d n)).obj
          ((pbcCompletedReduction T d n).obj K))
        (fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map
          (pbcReductionTransition (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K) ≫
          (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom.app
              ((pbcCompletedReduction T d n).obj K))
    IsDerivedLimit
      (K := fun n ↦ M.obj (op n))
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op) K
```

The proof was `by sorry`. No additional proof-local commands or helpers followed
the module's original variable declaration.

## New

```lean
theorem pbc_actual_completed_reduction_reconstruction
    [HasCountableProducts (PbcCompletedDerived T d)]
    (K : PbcCompletedDerived T d) (hK : PbcIsIntrinsicallyComplete T d K) :
    let M : ℕᵒᵖ ⥤ PbcCompletedDerived T d :=
    Functor.ofOpSequence
        (X := fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d n)).obj
          ((pbcCompletedReduction T d n).obj K))
        (fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map
          (pbcReductionTransition (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K) ≫
          (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom.app
              ((pbcCompletedReduction T d n).obj K))
    IsDerivedLimit
      (K := fun n ↦ M.obj (op n))
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op) K
```

The body is a complete proof from the existing Koszul quotient comparison,
strict Roos theorem and normalized evaluation/scalar adjunction interfaces.
Private helper definitions are real constructions and private helper theorems
are completely proved. Added elaboration options and local attributes affect
only this file; the only additional variable command is confined to the closed
`ScalarComputation` section.

## Users

The following includes every module reported by `tools/downstream.py
Sheaf.Paper.ActualCompletedReductionReconstruction --uses
pbc_actual_completed_reduction_reconstruction`, including the transitive import
closure. Only the item and `Sheaf.Paper.IntegralCanonicalTruncations` mention the
theorem itself. No consumer requires an edit because its signature, visibility,
and public imports are identical. Holder entries record the current claim files.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | Q3 | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | V1 | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.FinitePullbackLocalizationCohomology | V7 | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | K9 | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | R9 | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | D9 | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ActualCompletedReductionReconstruction | P8 | Proof completed; signature unchanged. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.AmbTateRootProjectionReduction | R4 | No adaptation: public interface unchanged. |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | P5 | No adaptation: public interface unchanged. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.AutomorphismCompletionUnitComparison | E2 | No adaptation: public interface unchanged. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ClopenRoosIntegralDescent | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CoefficientHeart | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CommonStageCalculus | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CommonStageLisse | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CommonStageLocallyFree | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompleteCompactSupportProetale | S3 | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompletedCoefficientPresentationTransport | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | F6 | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompletedExchangeCoherence | S9 | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompletedLineTensorCoherence | J6 | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompletedPerfectScalarPullback | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompletedPullbackTensorComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CompletedTensorScalarLinearity | E7 | No adaptation: public interface unchanged. |
| Sheaf.Paper.CondensedERealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CurveMiddleExtension | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DerivedPullbackTensorHom | S4 | No adaptation: public interface unchanged. |
| Sheaf.Paper.DerivedPullbackTensorIso | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.EffectiveComparisonRealizationModels | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.EtaleIsoDescent | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteCoefficientPoint | T3 | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteOpenProductSwap | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteProductFieldCoefficientDescent | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteProperProductTranspose | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FinitePullbackTensorComparison | F8 | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | P7 | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteTateSiteDescent | T4 | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteWindow | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FourierAdicArtinSchreier | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | A5 | No adaptation: public interface unchanged. |
| Sheaf.Paper.GeometricStalkPerfect | T5 | No adaptation: public interface unchanged. |
| Sheaf.Paper.IdentificationFibreAdjunction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralCanonicalTruncations | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralCoherenceTower | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralCompositionCounitImages | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralLineReductionRestriction | J8 | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralModels | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralTStructure | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IntrinsicQbarCategory | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.InverseImagePullbackComparisonDerived | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IsomorphismComparisonNatural | R6 | No adaptation: public interface unchanged. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.IsomorphismScalarTensorKFlatModel | S6 | No adaptation: public interface unchanged. |
| Sheaf.Paper.KummerAdditivity | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.LocalizedTStructure | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | K9 | No adaptation: public interface unchanged. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | S4 | No adaptation: public interface unchanged. |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | G5 | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcCommonStageCones | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcConeIndependence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcDescentFunctors | J5 | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | A8 | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcFiniteRawScalarComparison | S7 | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcFiniteStageKaroubian | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcIdempotentCompleteTriangulation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcPairFunctorShiftCoherence | A3 | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcQbarCategory | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcQbarCompletedPullback | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcQbarIdempotentComplete | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcScalarExtension | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcSupportCondition | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PbcVerdierAxioms | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointAutomorphismRestrictionNatural | R7 | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointExactDerivedModel | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorBasic | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointFibreEquivalence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointIntegralPerfectRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointIntegralSectionsConservative | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointQbarFibreShiftDescent | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointRationalFibreExact | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointRationalSectionsHom | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointRationalSectionsLattice | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PointTransformationCoefficientDescent | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PulledReductionStrictTowerComparison | M1 | No adaptation: public interface unchanged. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PurityConventions | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PurityCoprojection | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PurityFiniteKummerLevel | A9 | No adaptation: public interface unchanged. |
| Sheaf.Paper.PurityFiniteOpenIntervalDescent | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PurityRankOneLocalCalculation | G6 | No adaptation: public interface unchanged. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | No adaptation: public interface unchanged. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.QbarIdempotentComplete | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.QuotientSystemMixedCoherence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.RealSheafSections | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.RealWeilSheaves | R8 | No adaptation: public interface unchanged. |
| Sheaf.Paper.RealizationCompletedPull | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.RealizationScalarFunctor | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ScalarExtensionExactIntrinsic | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | P8 | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfConstructibleCanonicalCompleteness | G2 | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfConstructibleHeart | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfExactPullbackCounitNormalization | G9 | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfIntegralConstructibleLinear | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfIntegralConstructibleTriangulated | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfRationalBoundedConeTorsion | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfRationalizationKaroubi | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfScalarExtensionComposition | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SfWeilSheafComplex | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SitePerfectComplex | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | No adaptation: public interface unchanged. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SupportedCupFunctoriality | P9 | No adaptation: public interface unchanged. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SupportedHomCocycleNormalization | H5 | No adaptation: public interface unchanged. |
| Sheaf.Paper.SupportedHomPullback | B8 | No adaptation: public interface unchanged. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.WeilComplexQbarIdempotentComplete | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.WeilKernelHenselianInertia | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.TraceFormula.IntegralComparisonCounitCharacterization | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | H7 | No adaptation: public interface unchanged. |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | No adaptation: public interface unchanged. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | No adaptation: public interface unchanged. |

## Status

landed 20261021T130114-L-2530709 2026-10-21 (merge of deliver/P8/Sheaf.Paper.ActualCompletedReductionReconstruction)
