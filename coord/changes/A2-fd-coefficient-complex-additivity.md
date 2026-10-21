# WeilConjectures.FdOrdinaryScalarTransport.complex

## Reason

Restore the zero-hole module quarantined by upstream synchronization a762b776d.
Its archived `FdOrdinaryScalarTransport.complex` fails to synthesize additivity
for coefficient restriction at the first composition adapter; the middle factor
then fails to synthesize zero-morphism preservation, and `completion` and the main
structure fail in consequence. Merely adding local additive instances or changing
backward transparency does not resolve the error.

Fix the intermediate module categories explicitly on the four existing functors
and on both canonical composition adapters. Supply their existing additive proof
instances, and ascribe the existing ordinary comparison to their composite type.
The definition still composes precisely the same three canonical isomorphisms in
the same order. All signatures, imports, normalization fields and data
constructions retain their meaning. The functor aliases zeta-reduce to the prior
functors; proof irrelevance identifies the additive instances. No data is chosen
from a new existence statement. The repaired file, including `completion` and the
main structure's `chi` field, compiles against the current server library.

## Old

```lean
def FdOrdinaryScalarTransport.complex {T : Scheme.{u}}
    {E L : Padic.FiniteCoefficientFields l Ω} {h : E ≤ L}
    (m : FdOrdinaryScalarTransport l Ω T h) :=
  Functor.mapHomologicalComplexCompIso (F :=
    completedOrdinaryScalarExtension l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T)
    (G := fdCoefficientTransport l (pbcFiniteField.{u} l Ω L) T) (Iso.refl _) (.up ℤ) ≪≫
  NatIso.mapHomologicalComplex m.comparison (.up ℤ) ≪≫
  (Functor.mapHomologicalComplexCompIso
    (F := fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T)
    (G := pbcExtend (pbcCompletedScalarMap l Ω T h)) (Iso.refl _) (.up ℤ)).symm
```

## New

```lean
def FdOrdinaryScalarTransport.complex {T : Scheme.{u}}
    {E L : Padic.FiniteCoefficientFields l Ω} {h : E ≤ L}
    (m : FdOrdinaryScalarTransport l Ω T h) :=
  let F : integralTowerModules l (pbcFiniteField.{u} l Ω E) T ⥤
      integralTowerModules l (pbcFiniteField.{u} l Ω L) T :=
    completedOrdinaryScalarExtension l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T
  let G : integralTowerModules l (pbcFiniteField.{u} l Ω L) T ⥤
      pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω L)) :=
    fdCoefficientTransport l (pbcFiniteField.{u} l Ω L) T
  let H : integralTowerModules l (pbcFiniteField.{u} l Ω E) T ⥤
      pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)) :=
    fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T
  let J : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)) ⥤
      pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω L)) :=
    pbcExtend (pbcCompletedScalarMap l Ω T h)
  letI : F.Additive := completedOrdinaryScalarExtension_additive l
    (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T
  letI : G.Additive := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω L) T
  letI : H.Additive := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω E) T
  letI : J.Additive := pbcExtend_additive (pbcCompletedScalarMap l Ω T h)
  let c : F ⋙ G ≅ H ⋙ J := m.comparison
  Functor.mapHomologicalComplexCompIso
      (V := integralTowerModules l (pbcFiniteField.{u} l Ω E) T)
      (W := integralTowerModules l (pbcFiniteField.{u} l Ω L) T)
      (W' := pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω L)))
      (F := F) (G := G) (H := F ⋙ G) (Iso.refl _) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (V := integralTowerModules l (pbcFiniteField.{u} l Ω E) T)
        (W := pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)))
        (W' := pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω L)))
        (F := H) (G := J) (H := H ⋙ J) (Iso.refl _) (.up ℤ)).symm
```

## Users

The standard downstream tool cannot index the absent item without `--allow-missing`;
its live-tree view omits quarantined consumers. The table below also scans the
archived module imports and their transitive consumers, preferring current Lean
sources when both versions exist. No consumer needs a source adaptation: the
comparison retains its inferred type and its three canonical factors. The category and functor arguments and existing proof
instances are supplied explicitly. The item's `completion` definition and `chi`
field themselves exercise the repaired comparison.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | existing claim; unchanged | Identical public interface and canonical maps; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.DualBaseChange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FdPullbackComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | existing claim; unchanged | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | existing claim; unchanged | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed in local claim records | Identical public interface and canonical maps; no adaptation. |

No target statement or meaning changes. DAG node
`def-fd-coefficient-comparison-datum` keeps its attachment, statement and dependencies.
Its proof remains empty because this node defines data and asserts no existence.

## Status

landed 20261021T125935-L-2461777 2026-10-21 (merge of deliver/A2/Sheaf.Paper.FdCoefficientComparison)
