# SystemLevelLeftExtension componentwise proof support

## Reason

The proof constructs finite limits and colimits componentwise, and needs the existing
scalar-restriction exactness instances before those constructions. Their three existing
declarations move earlier. Private helpers are inserted under `variable {B}`;
`variable (B)` then restores the explicit binder for the existing evaluation theorem.
The preflight conservatively classifies these section-command changes as an interface
change. Every existing public signature, definition body and visibility is preserved.
No target statement or definition used by a target changes its mathematical meaning.

## Old

The following declarations occur after `strictSystemTransition` in the original:

```lean
/-- Exactness of scalar restriction, with no flatness of the ring map.
Source: Stacks 03DA and 03DB (blueprint: lem-pur-system-level-left-extension).
Proof: the underlying abelian sheaf and all its maps are unchanged. Kernels and
sheafified cokernels therefore coincide with those before restriction. -/
theorem systemScalarRestriction_exact {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) ∧
    PreservesFiniteColimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) := by
  sorry

/-- Exact restriction preserves finite limits. Source: Stacks 03DA
(blueprint: lem-pur-system-level-left-extension). -/
instance systemScalarRestrictionLimits {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) :=
  (systemScalarRestriction_exact φ).1
/-- Exact restriction preserves finite colimits. Source: Stacks 03DA
(blueprint: lem-pur-system-level-left-extension). -/
instance systemScalarRestrictionColimits {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteColimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) :=
  (systemScalarRestriction_exact φ).2
```

After `strictRingSystemAbelian`, `B` is explicit and `systemEvaluation_exact` follows
immediately. There are no private componentwise cone/cocone constructors there.

## New

The same three scalar-restriction signatures and instance bodies occur immediately after
`strictRingSystemAbelian`; the theorem proof uses preservation and reflection through
`toSheaf`. The unchanged signatures above are the new signatures verbatim as well.
The new private componentwise cone/cocone constructors use implicit `B`, then the existing
public declarations resume with explicit `B`:

```lean
variable {B}
-- private, fully constructed componentwise cones and cocones
variable (B)
```

Private constructors have no holes and occur in no public signature or public definition.
All existing public definitions retain their original bodies. No downstream adaptation is
needed. The moved declarations and abelian existence theorem are mentioned only within
the item itself according to the source-only downstream scan with `--uses`.

## Users

The source-only downstream scan lists 513 transitive importers. Each is recorded below;
their statements continue to use exactly the same public interface. Holders are those in
`coord/claims` at preparation time. None is edited by this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.SystemLevelLeftExtension | M8 | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CanonicalWeilFundamentalRepresentation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint | P2 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientSystemDerivedComparison | Q2 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportDirectImageTriangulated | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | F8 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | Q3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | Z7 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | S1 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleWeilSheafEquivalence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | G9 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | R3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | A2 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | J3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | W7 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBound | K5 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineChartBounds | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.QbarOrdinaryAdjunction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | D3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RealSheafSections | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | E1 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | K9 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SfPreservationClass | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoefficientTowersAbelian | D5 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionBaseChange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedTowers | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint | Z5 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerInjectiveComponents | X8 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerLevels | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | K1 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | D8 | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Public signatures and data unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public signatures and data unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromyFrobenius | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalk | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Public signatures and data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Public signatures and data unchanged; no adaptation. |

## Status

landed 20261019T005347-L-2757127 2026-10-19 (merge of deliver/M8/Sheaf.CategoryTheory.SystemLevelLeftExtension)
