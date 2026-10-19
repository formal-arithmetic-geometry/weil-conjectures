# Sheaf.AlgebraicGeometry.SupportedKummerCartierPullback

## Reason

The static interface check requires this record for the added namespace-opening
commands, declaration-local elaboration options and private reassociation attribute.
The proof uses kernel lifts and monoidal morphism notation, so it opens Limits and
MonoidalCategory in addition to CategoryTheory. The five helper theorems, including
the generated reassociation theorem, are private and proved. No public signature,
public definition body, public import, notation declaration or instance is changed.
No target meaning changes and no consumer adaptation is needed.

## Old

The original namespace-opening command is:

```lean
open CategoryTheory
```

The existing public signatures are:

```lean
noncomputable def tensorPullbackUnitDualMap (h : T' ⟶ T) :
    (Modules.unit T')ᵛ ⟶ (Scheme.Modules.tensorPullback h).obj (Modules.unit T)ᵛ

theorem exists_tensorPullback_dual_toModules_iso
    (h : T' ⟶ T) {J : T.IdealSheafData} (hJ : J.IsInvertible)
    (hJ' : (J.comap h).IsInvertible) :
    ∃ e : (Scheme.Modules.tensorPullback h).obj J.toModulesᵛ ≅ (J.comap h).toModulesᵛ,
      tensorPullbackUnitDualMap h ≫
          (Scheme.Modules.tensorPullback h).map (Modules.dualMap J.toModulesι) ≫ e.hom =
        Modules.dualMap (J.comap h).toModulesι
```

The original theorem proof is `by sorry`. The existing public definition body is
retained verbatim.

## New

The namespace-opening command is:

```lean
open CategoryTheory Limits MonoidalCategory
```

The public signatures remain verbatim:

```lean
noncomputable def tensorPullbackUnitDualMap (h : T' ⟶ T) :
    (Modules.unit T')ᵛ ⟶ (Scheme.Modules.tensorPullback h).obj (Modules.unit T)ᵛ

theorem exists_tensorPullback_dual_toModules_iso
    (h : T' ⟶ T) {J : T.IdealSheafData} (hJ : J.IsInvertible)
    (hJ' : (J.comap h).IsInvertible) :
    ∃ e : (Scheme.Modules.tensorPullback h).obj J.toModulesᵛ ≅ (J.comap h).toModulesᵛ,
      tensorPullbackUnitDualMap h ≫
          (Scheme.Modules.tensorPullback h).map (Modules.dualMap J.toModulesι) ≫ e.hom =
        Modules.dualMap (J.comap h).toModulesι
```

The theorem has a complete proof. Declaration-local transparency options aid
elaboration and do not change its type. The private tensor naturality helper uses
`@[reassoc]` to generate the corresponding private associativity helper.
The three existing public imports are unchanged. Five redundant proof imports
are pruned, as listed in the report.

## Users

Generated from `tools/downstream.py` on 2026-10-19, with one row per downstream
module and the item itself. The only direct importer is
`Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`; it imports the item as a
proof dependency and currently has no textual use of either public declaration.
The declaration-use scan finds both existing names only in the item itself.
Every downstream module therefore retains exactly its previous public interface.
Holders are the current claim records at the time of this audit; unclaimed modules
have no claim record. No module other than the item is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedKummerCartierPullback | M3 | Proof completed; namespace opens and declaration-local elaboration options added. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | V4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | G6 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | G1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | D3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | E3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | T9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | S8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | C7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | B5 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | M1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | X7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange | Y6 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | J4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | H5 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CanonicalWeilFundamentalRepresentation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CartesianCoefficientTwists | Q4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefficientFiniteDescentHom | E4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefficientFiniteDescentLisse | F1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefficientHeart | X8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefficientHeartCommonStratification | F2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefficientHeartFiltration | P4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefficientHeartGeneration | P7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefficientHeartSmall | F3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefficientHeartTriangulated | Y5 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactSupportReductionTower | F8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ConstructibleCompactness | U7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | Z7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ConstructibleExtContinuity | U8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | P8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | R2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | T2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DetIndHeartIISums | C5 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DiagonalTowerLimit | G3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DiagonalTowerSystem | H4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DirectImageChangeRingTranspose | J2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | F8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | N1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleGeometricBiduality | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.EtaleWeilSheafEquivalence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ExceptionalCoefficientComparison | S4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | G7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | G9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteFieldExceptionalPreservation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteProperLocalizing | V9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteRingSectionDeformation | V3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteTateSiteDescent | V9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteWindow | W5 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteWindowBounded | C1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FormalClosedSupport | Q9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FormalClosedSupportII | M2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FormalClosedSupportIILimits | W6 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | R3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FrobeniusGeometricExchange | A2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.FrobeniusSquareExchange | J3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IndConstructibleExtensions | K4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IndConstructibleFilteredColimits | M1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IndHeartCanonicalPresentation | W8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IndHeartFullFaithfulness | M2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IndHeartIIVanishing | E9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | W7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralConstantModelHeart | C2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralConstructibleExt | J9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralExtensionByZero | A3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralHeartLocalModel | C3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | S3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralModels | D4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralModelsOperations | N1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralTensorShriek | F2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralTwistBaseChange | J4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntegralTwistScalarCoherence | N4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | C3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.MateOpenRestriction | D7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | P2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.OpenImmersionLocalizing | X5 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperHeartBound | K5 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperHeartBoundLattice | G2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperHeartBoundTorsion | J4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | Y2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityConventions | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | R2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.QbarTwistCommonStage | R1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.QcqsCompactSupportRealization | D3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RationalClosedSupportConstructible | C1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RealSheafSections | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.RestrictionLocal | R3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | K9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SfPreservationClass | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.SystemOperationExchangeRealization | K1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TateTwistLocallyFree | S7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceBaseChangeFirst | E1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TwConventions | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.TwistPreservesFiniteness | G5 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.UnboundedLocalizingPullback | Y7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.UniformConstructibleExt | X9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.UniformConstructibleExtIntegral | K4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.WeilCompactSupportCohomology | D8 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | U9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | G1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | R3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | M1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Z9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.FieldTensor | N1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | T4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | F4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.Targets.VectorBundlePurity | F6 | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| TargetsCheck | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromyFrobenius | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalk | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.Statement | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged; existing declaration types, values and public imports preserved. |

## Status

landed 20261019T005341-L-2755654 2026-10-19 (merge of deliver/M3/Sheaf.AlgebraicGeometry.SupportedKummerCartierPullback)
