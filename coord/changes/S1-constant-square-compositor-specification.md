# AlgebraicGeometry.ProEtale.StrictTower.moduleSquareG

## Reason

Keep the canonical square compositor folded during categorical pasting proofs. With the
original composite exposed, the ordinary coefficient-change square proof exhausted the
file/kernel limits while comparing nested natural isomorphisms. The compositor now takes
its value from a proved unique specification that requires equality to exactly the
original composite. `moduleSquareG_eq` is a proved public equation for that specification.
No unproved existence theorem supplies data, and no mathematical choice has changed.
The analogous varying-ring compositor already uses this interface.

`FiniteOpenBaseChangeNormalized` was unclaimed when checked. Its existing signatures,
visibility and public imports are retained. The only existing definition body changed is
`moduleSquareG`. All target statements keep their text. This definition change reopens the statement-meaning
review for targets that use it, as required by AGENTS.md section 4. The proved equality
fixes precisely the original composite and supplies the equivalence for that review;
the independent reader must check it.

## Old

```lean
noncomputable def moduleSquareG {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    modulePullback B i ⋙ modulePullback B r ≅ modulePullback B p ⋙ modulePullback B k :=
  (moduleGComp B r i).symm ≪≫ eqToIso (congrArg (modulePullback B) h.symm) ≪≫
    moduleGComp B k p
```

## New

```lean
noncomputable def moduleSquareG {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    modulePullback B i ⋙ modulePullback B r ≅ modulePullback B p ⋙ modulePullback B k :=
  (moduleSquareG_existsUnique B k r p i h).choose
```

The added proved theorems `moduleSquareG_existsUnique` and `moduleSquareG_eq` state the
unique equality specification and its defining equation. Their DAG node is
`lem-fix-constant-square-compositor-specification`. The ordinary square proof passes
this equality as an explicit argument to generic transport, so its kernel check does
not convert the expanded sheaf-module composites.

## Users

Refreshed on 2026-10-20 from `tools/downstream.py` for the current shared sources:
755 downstream modules, plus the changed module and the new helpers.
The textual strict-compositor users are `FiniteOpenExchangeScalars` and
`CompleteProetaleStrictTowerRealization`; `VaryingRingProperOpenArrows` uses its separate
varying-ring compositor. Every existing statement has the same meaning by the proved
`moduleSquareG_eq`. No consumer source adaptation is included. Claim holders below
are the current shared records; expiry is identified explicitly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportOpenFactor | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | D3 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | D2 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | F7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.ExceptionalBaseChangeCartesianOpenInjectiveAcyclic | T6 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized | unclaimed | Compositor repaired; same signature and proved explicit formula. |
| Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars | C9 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.FixSiteOpenExchange | H3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.FormalPuncturedSections | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | P9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.OpenBaseChangeSiteTransport | P7 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalizationFilteredSection | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison | M5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | A2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | X5 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | Q5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | D5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.PunctualPurityTraitTest | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | S1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | K1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | P5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | M8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows | F5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | H2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | K4 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingOperations | U8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | C7 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | V7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | F9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | D9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicClosedConstructible | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | B8 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | T4 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | C7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | G5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | C8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | Y5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | Q8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | Q9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | R5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | G3 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CartierClassAgreement | U5 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ChernFlagFormula | G4 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | R3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | K6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | Y2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | R7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactFiberStalk | E7 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | U3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportExchangeTransport | B4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | K4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | R6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | Q4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | P2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | R9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportSiteCoherence | U2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompleteCompactSupportProetale | J3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | Y7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | T1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompletedPullbackTensorComparison | S1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | Y9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | D2 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | W3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | D4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | J4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConstantWeilStructure | E1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConstantWeilStructureStageIndependence | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | R2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | H1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | X7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ConstructibleTruncations | Z8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | E6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | K2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | D8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | W2 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DerivedPullbackTensorIso | W3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | J2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | G8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleCompactScalarCoherence | V5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | R2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | N1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | U4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | Z5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | Z6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | D6 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | Q3 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | N4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | P8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | F1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | U7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | G1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | V9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | C2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteClosedShriek | K6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | M1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | M3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | A2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Q5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | S5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | G9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | M4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | U1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | N2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteExtensionReductionConeBound | R8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | D7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | N3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteProjectionActionLaws | X9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | W7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | G9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | N4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | Y6 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteSystemPullbackCoherence | K5 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | X3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | V8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | A5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | D9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | F4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralCoherenceTower | B2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | X2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | W7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | W5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | W3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | K2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | P1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | S4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | M3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | M1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | Y8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | E9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | B4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | F5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | V4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | A5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralPullbackComposition | A7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | B6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | H7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | Z7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | F7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | D4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | Q5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | R6 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | A6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.MateOpenRestriction | U2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | E5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | T8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | E4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | D2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | E9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | T6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | P9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperOpenCoefficientMate | W8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperOpenTowerComparison | Q4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | T7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | J9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PuncturedDerivedCompletionSections | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | R3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityDivisorClass | J7 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityDncComparisons | G3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityFrameIndependence | A4 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | H4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityGysinStructure | F1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityRelativeKummer | F4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PuritySourceTransports | V6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.QbarCompactSupportBaseChange | S4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.QbarOrdinaryAdjunction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | D3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | T2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | P2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | U7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | Z9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalStalkExact | A7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RefinementExchangeCoherence | P3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | B6 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | G5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | F9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SfBidualityClass | C6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | E1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | K9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | T3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | W3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | J3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | M4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | Y6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SupportedHomPullback | H4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | Y5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | F5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | K1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.SystemTensorMateArrows | B7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | N2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | U5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | C2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | J8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | B2 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.VectorBundlePurity | S1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | A8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | A9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | E7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | S2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | U8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | Q8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | P7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | J7 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | U2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.RingTheory.CompleteLocalConnectednessBound | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.RingTheory.NormalPuncturedHypersurfaceConnected | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | W9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | U8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | U9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.OpenBaseChangeDerivedUnit | S1 | Proved in this delivery; compiled with the repaired compositor. |
| Sheaf.SecSmoothPurity.OpenScalarExchange | S1 | Proved in this delivery; compiled with the repaired compositor. |
| Sheaf.SecSmoothPurity.OrdinaryRestrictionPullbackSquare | S1 | Proved in this delivery; compiled with the repaired compositor. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | M9 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | G1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SecSmoothPurity.TensorPullbackSquare | S1 | Proved in this delivery; compiled with the repaired compositor. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | N2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | V1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | J5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | U6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | V5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | P6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | K9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | W2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | M6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | M7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | B8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | B5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | N3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | B5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | M2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | Z8 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | W8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | P5 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | Q8 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | R1 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | T9 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | R5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | J1 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | M2 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | K2 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | X5 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | E4 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | T9 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | S6 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | D6 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.Targets.VectorBundlePurity | F6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | Y7 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | Y3 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | X6 (expired claim) | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | H1 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | T2 | Same meaning by moduleSquareG_eq; no source adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| TargetsCheck | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.Statement | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same meaning by moduleSquareG_eq; no source adaptation. |

## Status

landed 20261019T192830-L-1874347 2026-10-19 (merge of deliver/S1/Sheaf.SecSmoothPurity.OpenScalarExchange)
