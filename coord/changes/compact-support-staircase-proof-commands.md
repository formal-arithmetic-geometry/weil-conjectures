# compactSupportStaircaseInterchange normalization sharing

## Reason

The completed staircase proof exposed a slow existing selector definition. Profiling
found kernel checking of its generated choice proof and selector taking about 24 seconds,
with repeated large normalization predicates in later choice specifications pushing the
file with the axiom probe over 60 seconds. The apparent lint cost was the module linter
waiting for those asynchronous kernel checks. Naming the complete normalization predicate
and its existence theorem shares this expression across the selector and pasting proofs.
All normalization clauses, the same chosen underived family, and all existing signatures
are preserved. The chosen data is determined by precisely the original normalization.

The proof also uses local irreducibility attributes for the derived-functor constructions
and disables the unused-simp-argument linter. These commands affect elaboration and
warnings only. No consumer statement or target changes mathematical meaning.

## Old

```lean
noncomputable def compactSupportStaircaseInterchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : CommSq k r p i) :
    R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (Classical.choose (Classical.choose_spec (unboundedProperOpenInterchange A))) k r p i sq
```

## New

```lean
noncomputable def compactSupportStaircaseInterchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : CommSq k r p i) :
    R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (Classical.choose (compactSupportStaircaseInterchange_exists A)) k r p i sq
```

The new definition `compactSupportStaircaseInterchangeNormalization` is the complete
predicate from the second existential in `unboundedProperOpenInterchange`, with the
identical chosen underived family. Its named existence theorem is proved directly by
`Classical.choose_spec`. Both are attached to the existing staircase node. The two
pasting calculations now use this named predicate's specification. The old and new
selectors are definitionally equal: only the representation of the predicate and its
proof differs. The other two existing definition bodies and all existing signatures
are unchanged. A separate Lean `rfl` test of the selector against its original
expression compiled successfully in 16.8 seconds. The unchanged sole direct consumer,
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`, compiled against
the delivered overlay in 7.0 seconds. Thus the repair changes no target meaning.

Local irreducibility commands cover `rightDerivedLowerStarComp`, the exact-derived
comparison constructors, the open-extension constructors, and the three staircase
definitions. The linter option is `linter.unusedSimpArgs false`. These commands have
no downstream effect. The new structural-coherence module and its one public theorem
are described in their new DAG node.

## Users

`tools/downstream.py Sheaf.Paper.CompactSupportStaircaseExpansion --uses
AlgebraicGeometry.Etale.compactSupportStaircaseExpansion` lists the item as the only
textual user of the theorem. The sole direct importer is
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`. The table below
also records every transitive downstream module from that command. No consumer
statement or definition changes meaning, and no consumer adaptation is required.
Holders are recorded from the current shared claims when this record was written.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompactSupportStaircaseExpansion | T8 | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CompositeIntegrationCounit | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.DeltaProperPushforward | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | N1 | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.EtaleGeometricBiduality | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ExceptionalCoefficientComparison | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteExceptionalInternalHom | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteFieldExceptionalPreservation | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TwConventions | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.WeilOne | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.WeilVerdierPreservationStrata | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same signatures and definitions; no adaptation needed. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same signatures and definitions; no adaptation needed. |
| TargetsCheck | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.Statement | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same signatures and definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same signatures and definitions; no adaptation needed. |

## Status

landed 20261019T112538-L-3953653 2026-10-19 (merge of deliver/T8/Sheaf.Paper.CompactSupportStaircaseExpansion)
