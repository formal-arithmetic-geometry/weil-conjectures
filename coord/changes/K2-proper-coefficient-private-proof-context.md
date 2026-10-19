# AlgebraicGeometry.ProEtale.CondensedRing.proper_image_localizing_proper_coefficients

## Reason

The coefficient proof adds private helpers, a section of standing scheme variables,
and a local irreducibility attribute to avoid unfolding the large canonical functors
during elaboration. The static preflight treats these commands conservatively as an
interface change and requires this record. Every existing public signature, data
definition, public import, and docstring is identical. All new declarations are
private and fully proved or have explicit constructed data. No instance is exported.

## Old

After `proper_image_localizing_proper`, the original file proceeds directly to the
coefficient theorem. There is no additional attribute or variable section. Its
coefficient theorem has the identical signature in the delivered file and proof
`by sorry`.

## New

The new local command before the private coefficient helpers is:

```lean
attribute [local irreducible] Functor.rightDerivedFunctor upperStarFromPoint
```

The shared binders for the private finite, integral and rational cases are exactly:

```lean
section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]

include k
```

This section ends with `end Coefficients` before the public coefficient theorem.
The local irreducibility attribute affects elaboration in this module only; it does
not change either functor's definition or an importer's reducibility settings.
The variables and `include k` affect only the three private lemmas in that section.
The complete coefficient proof invokes these lemmas, including the explicitly
constructed coefficient isomorphisms for the Q_l and Z_l cases. No target statement
or definition that a target uses is changed. No consumer adaptation is necessary.

## Users

The table is the complete transitive output of
`python3 tools/downstream.py Sheaf.SixFunctors.ProperImageLocalizingProper --names`
on 2026-10-19. Holders were read using the project's claim-holder API. The only
external textual user of `proper_image_localizing_proper_coefficients` is
`Sheaf.Paper.UnboundedBaseChangeExtension`; it receives the identical statement.
The six direct importers retain the identical public API and public imports.
All rows have the same empty interface effect; no consumer is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | W9 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | U4 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | U2 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | H2 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | M6 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| TargetsCheck | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Z8 | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | B4 | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | C1 | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | C3 | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | D2 | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Existing signatures, data and exports unchanged; no adaptation. |

## Status

landed 20261019T192759-L-1867170 2026-10-19 (merge of deliver/K2/Sheaf.SixFunctors.ProperImageLocalizingProper)
