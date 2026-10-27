# ToricMonoid: completed-model public imports

## Reason

`CompleteToricModel` publicly imported the completed-chart theorem module, even though
none of its declarations uses that module's three declarations. The model defines its
own monomial with independent universes. This prevents the completed-chart theorem
from importing the existing coefficient-surjection, principal-kernel or more general
pointwise completion theorem: each of those uses `CompleteToricModel`.
Remove this unused upward theorem dependency. Preserve the old imported public
prerequisites explicitly. No definition, theorem signature, instance or attribute changes.
The model is unclaimed. No source-library module changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LogRegularCompletedChart
```

## New

```lean
public import Sheaf.AlgebraicGeometry.LogEtaleRestrictionStalkComparison
public import Sheaf.AlgebraicGeometry.LogRegularSharpChart
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.RingTheory.AdicCompletion.LocalRing
```

The existing public import of `LogRegularSaturationNormality` also stays. Thus all
public prerequisites previously obtained through `LogRegularCompletedChart` stay
available. Only its `sharpChartRingMap`, `completedLocalModelMonomial`, and
`exists_completed_chart_of_logRegular` cease to be incidental model re-exports.
No model consumer refers to them (checked by repository-wide declaration searches).
Consumers needing that theorem already import its module directly.

## Users

The table includes the full downstream list from `tools/downstream.py` and the
completed-chart module that becomes a new proof consumer. The 16 direct importers
are compiled, unchanged, against the new model. Their temporary source copies
are removed before delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CharacteristicZeroLogResolutionIndependence | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.CompleteLocalRigidificationComparison | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.EquivariantLogSmoothFanRegularization | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.FieldLogSmoothGabberModification | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.FormalChartGeometricRegularity | V1 | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.AlgebraicGeometry.FreeCharacteristicRelativeNCCriterion | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.GabberAbelianStageToricChart | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.GabberAbsoluteEquivariantModification | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.GabberLogBlowupRegularization | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.KummerBoundaryRestriction | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.KummerGCoverFSBaseChange | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.LogBlowupNormalization | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.LogMonoidalAssociatedPoints | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.LogRegularCompletedChart | unclaimed | Now imports model and pointwise theorem privately; main proof completed. |
| Sheaf.AlgebraicGeometry.LogRegularGenerization | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.LogRegularPairRegularPullback | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.LogSmoothInvertibleTorsionLogRegular | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.LogSmoothLogRegular | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.LogSmoothPreservesLogRegularity | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.NoetherianLogPairStrictResolution | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.PointwiseLogRegularCompletion | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.AlgebraicGeometry.PrimitiveMonomialTraitGeometry | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.RationalToricCompletionRegularMap | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.RigidifiedQuotientTowerComparison | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.SmoothMarkedLogChart | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.AlgebraicGeometry.VeryTameQuotientLogRegular | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.RingTheory.CohenMonoidSubstitutionParameter | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.CohenMonoidSurjectionPrincipalKernel | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.CompleteModelFaceQuotients | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.CompleteToricBoundaryClassInjectivity | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.RingTheory.CompleteToricFaceStrata | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.CompleteToricFacetValuations | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.CompleteToricLocalizedUnitDivisorLift | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.CompletedChartCoefficientSurjection | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.CompletedMonomialTransverseParameter | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.FacetLatticeSupportedCoordinateCover | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.FilteredMonoidCoefficientLimit | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.PolynomialMonoidLiftStratum | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.PositiveMonoidAdicFiltration | P3 | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.SharpConePrimitiveFacetPreparation | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.RingTheory.SupportedCoordinateCoverUnitsPrimes | unclaimed | Direct importer: compile original source against the changed model; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.TraceFormula.CompleteToricKatoRecognition | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.TraceFormula.CompleteToricMonomialFactors | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.TraceFormula.LogRegularDesingularization | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.TraceFormula.LogRegularDivisorialStructure | unclaimed | Declarations unchanged; no use of the three removed re-exports. |
| Sheaf.TraceFormula.LogRegularToricRefinement | unclaimed | Declarations unchanged; no use of the three removed re-exports. |

## Status

landed 20261026T091647-L-3361593 2026-10-26 (merge of deliver/H1/Sheaf.AlgebraicGeometry.LogRegularCompletedChart)
