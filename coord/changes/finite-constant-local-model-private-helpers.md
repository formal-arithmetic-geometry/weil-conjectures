# FiniteConstantLocalModel private proof helpers

## Reason

The stage-3 preflight requires a change record for the added `omit ... in` commands.
These commands remove unused section hypotheses from private helper theorems only.
The private helper instances give finite-colimit preservation and additivity locally
inside this module. All existing public signatures, definitions and public imports
are identical. No target statement or definition changes, and no consumer needs an
adaptation. The proof-only imports expose nothing to importers under the module system.

## Old

The existing module had no private helper instances or hypothesis-omission commands.
Its nondeclaration commands, as read by the interface checker, were:

```lean
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
attribute [instance] scalarRingObj_comm
attribute [instance] scalarCoefficientHom_isMonHom
attribute [instance] scalarConstant_comm
```

## New

The nondeclaration commands are now:

```lean
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
attribute [instance] scalarRingObj_comm
attribute [instance] scalarCoefficientHom_isMonHom
attribute [instance] scalarConstant_comm
omit [IsCommMonObj Λ] in
omit [MonObj Λ] [IsCommMonObj Λ] in
omit [MonObj Λ] [IsCommMonObj Λ] in
omit [IsCommMonObj Λ] in
omit [IsCommMonObj Λ] in
omit [IsCommMonObj Λ] in
```

Nine proved private instances are added: `scalarConstant_preservesFiniteColimits`,
`scalarExtension_preservesFiniteColimits`, `scalarExtension_additive`,
`pointMod_preservesFiniteColimits`, `pointMod_additive`, `scalarFieldHom_isIso`,
`scalarFieldHom_isMonHom`, `plainPullback_additive`, and `plainPullback_finiteColimits`. Their visibility is private;
none changes an existing declaration's type. Two private reducible definitions supply
braiding instances inside scalar-interface proofs. The `omit` commands bind only the
immediately following private theorem.

Private irreducible definitions `plainPullback`, `plainPullbackIso`, `plainRegularIso`,
`plainPullbackComp` and `evaluationCoordinates` package the constructed pullback and its
comparison isomorphisms. Their proved API avoids repeated unfolding of transported
monoidal structures. Generic point and rank helpers, and the abstract zero-indicator
argument, are proved in the same module; there are no new public declarations.
The concrete normed-field instance `counterexampleNormedField` is constructed by
`NormedField.induced`, rather than chosen from an existence theorem.

## Users

The read-only `tools/downstream.py` scan found the following transitive consumers.
The effect column follows from preservation of all existing signatures and public imports,
and from private visibility of every added helper. No forced adaptations are delivered.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | A9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | G3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | H9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian | J9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | X7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicClosedConstructible | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicConstructibleFiniteReductions | Y8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicResidueLissePerfectLift | V6 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AdicStratifiedPerfect | P5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | H5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CoefficientFiniteDescentHom | E4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | U5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CoefficientHeart | X8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CoefficientHeartFiltration | P4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CoefficientHeartGeneration | P7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CoefficientHeartTriangulated | Y5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CompactificationLocalizing | F4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ConstantModelTorAmplitude | G4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ConstructibleCompactness | U7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | Z7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ConstructibleExtContinuity | U8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | P8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.DetIndHeartIISums | C5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.DiagonalTowerLimit | G3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | S1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | N1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ExceptionalCoefficientComparison | S4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | G7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteComparisonLocalizing | V7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteFieldExceptionalPreservation | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | U3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteProperBaseChange | U4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteProperLocalizing | V9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteTorInternalHomAnyField | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteWindow | W5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteWindowBounded | C1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FormalClosedSupport | Q9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FormalClosedSupportII | M2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FormalClosedSupportIILimits | W6 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IndConstructibleExtensions | K4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IndConstructibleFilteredColimits | M1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IndHeartCanonicalPresentation | W8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IndHeartFullFaithfulness | M2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IndHeartIIVanishing | E9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | V4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralConstantModelHeartClosure | H7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralConstructibleCompactness | E7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralConstructibleExt | J9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralConstructibleHeart | P1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralHeartDualizable | C5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralHeartLocalModel | C3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralModels | D4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IntegralStratumExtBound | K1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.InterchangeProperPasting | S4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.InternalHomPullback | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.MateOpenRestriction | D7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | T2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.OpenImmersionLocalizing | X5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProperHeartBound | K5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProperHeartBoundReduction | Y5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityCoprojection | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RationalClosedSupportConstructible | C1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | Z5 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RationalStalkExact | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.RestrictionLocal | R3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SfPreservationClass | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SmoothTrace | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TwConventions | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.UnboundedLocalizingPullback | Y7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.UniformConstructibleExt | X9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.UniformConstructibleExtIntegral | K4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.UniformConstructibleExtRational | E3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.VerdierExchange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.WeilOne | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Z9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.FieldTensor | N1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.FiniteCompactProetale | A2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.FlatModel | A3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.FlatModelGeneration | S3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | B8 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | F4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| TargetsCheck | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.Statement | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No adaptation: existing signatures and public imports are identical; added helpers are private. |

## Status

landed 20261020T051112-L-1561764 2026-10-20 (merge of deliver/C9/Sheaf.AlgebraicGeometry.FiniteConstantLocalModel)
