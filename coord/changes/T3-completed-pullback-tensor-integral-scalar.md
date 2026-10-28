# canonicalIntegralPullbackTensor and canonicalIntegralPullbackTensor_scalar

## Reason

The assigned module has one hole: the integral scalar compatibility square. Existing
completed quotient realization theorems already give its proof, but imported the parent
comparison module, which imports this construction. Extracting the existing integral
constructor breaks that import cycle without introducing a new comparison or proof hole.
The two import-adapted modules and the normalization module were checked on the
current server and are unclaimed.

## Old

The three declarations `WeilConjectures.pullbackTensorComparisonCounits`,
`WeilConjectures.pullbackTensorReferenceComparison`, and
`WeilConjectures.canonicalIntegralPullbackTensor` were declared in
`Sheaf.Paper.CompletedPullbackTensorConstruction`.

`CompletedComparisonQuotientRealizationDefs` used:

```lean
public import Sheaf.Paper.CompletedPullbackTensorComparison
```

`ScalarExtensionTowerComparisonData` used:

```lean
import all Sheaf.Paper.CompletedPullbackTensorComparison
```

`canonicalIntegralPullbackTensor_scalar` had its existing unchanged signature and
proof `:= by sorry`.

## New

The same three declarations, with their original signatures and bodies verbatim, are
in `Sheaf.Paper.CompletedPullbackTensorIntegralConstruction`; the assigned module
publicly imports it, preserving the existing API. The proved private sequence-ring
identification is extracted with them. The two imports above become respectively:

```lean
public import Sheaf.Paper.CompletedPullbackTensorIntegralConstruction
import all Sheaf.Paper.CompletedPullbackTensorIntegralConstruction
```

The scalar theorem uses good representative essential surjectivity, existing quotient
normalization, canonical identification, and the existing scalar limit-image theorem.
The same limit arrow equals each scalar composite; transitivity and full-subcategory
hom extensionality give the original statement. No definition or instance is changed.

Four DAG references to the broad comparison node are narrowed to the new integral
constructor node. Their statement-change records preserve the old statements and
include every current citer. This changes only which node owns the unchanged map:
none of these realization lemmas assumes scalar compatibility or common-stage descent.
The construction node's attachment and proof route are updated to match the extraction.

Profiling found the parent and normalization files near or above the 60-second
limit. Local irreducibility barriers were tried first, but were insufficient.
The parent's existing `CoherentSystems` section, including its nine public
declarations and proved private helpers, is extracted verbatim into
`CompletedPullbackTensorCoherentConstruction`. The parent publicly re-exports it
and imports its private proof helpers with `import all`. No signature or proof
body in this extracted section changes. The evaluation-data node attachment is
retargeted to this module.

The unclaimed `CompletedComparisonQuotientNormalization` retains its statement
and its complete naturality proofs. Its existing model, reconstruction and
invertibility helpers are extracted verbatim into
`CompletedComparisonQuotientNormalizationModels`. The new, fully proved theorem
`WeilConjectures.CompletedQuotient.completedComparisonQuotientModels` assembles the
first three parts of the old conclusion using the same proof. The original
theorem obtains those parts and supplies its existing naturality proof. The new
node records this strictly smaller model statement and the old node records the
assembly. This introduces no hole or new choice of mathematical data. Both files
retain local irreducibility for the calculus and its tensor, pullback and
reduction realizations; no public attribute is changed. The assigned module uses
the same local calculus barrier in its scalar section. No profiler or linter
suppression is retained as a timing workaround. Unused proof imports are removed
after the extractions; the original parent's public imports are retained. The
final consumer check explicitly includes the current comparison and its finite
and tower evaluation chain, avoiding an older published comparison artifact
which still owned the moved declarations.

## Users

The table includes every textual consumer of the moved names in the downstream import
closure, every direct importer of an adapted module, and the adapted modules themselves.
No consumer statement changes. Direct importers are compiled against the overlay;
unchanged verification copies are removed before delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.CanonicalTateNaturalityLaws | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.CompletedComparisonCanonicalIdentification | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.CompletedComparisonQuotientNormalization | unclaimed | Existing model proofs extracted into a proved helper; original theorem combines models with its unchanged naturality proof. |
| Sheaf.Paper.CompletedComparisonQuotientRealization | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.CompletedComparisonQuotientRealizationDefs | unclaimed | Public import points to integral constructor; no declaration or body changes. |
| Sheaf.Paper.CompletedComparisonScalarLimitImage | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.CompletedPullbackTensorComparison | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.CompletedPullbackTensorConstruction | T3 | Re-exports the constructor and coherent declarations; proves the existing scalar theorem. |
| Sheaf.Paper.CompletedPullbackTensorNaturality | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.CompletedQuotientReductionPresentation | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationB | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.DerivedPullbackTensorConstraints | M1 | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.DerivedPullbackTensorIso | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.IntegralOpenPullTensorReduction | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.IntegralOrdinaryTensorPullbackNormalization | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.IntegralProjectionOpenTensorCoordinates | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.IntegralProjectionProperFactorReduction | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.IntegralProperTensorPullbackReduction | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.IntegralTensorPullbackAugmentation | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.PodCompletionTensorNormalization | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | G8 | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.ProjectionFormulaCoherence | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.RationalProjectionTensorCompatibility | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.RationalProjectionTensorModels | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.RelativeKunnethConstructions | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.ScalarExtensionQuotientAssociation | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.ScalarExtensionQuotientAssociationDegreeData | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | M3 | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.ScalarExtensionTowerComparisonData | unclaimed | Private import now points to integral constructor; same private ring-map identification proof. |
| Sheaf.Paper.ScalarExtensionTowerComposition | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.ScalarExtensionTowerRealizationData | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.SixFunctors.CompletedOpenCartesianIdentity | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.SixFunctors.OpenBaseChangeSquareData | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.SixFunctors.OrdinaryOpenFiniteEvaluation | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |
| Sheaf.SixFunctors.ProperSupportStepBounds | unclaimed | Unchanged signatures and canonical morphisms; re-export through the extracted constructor. |

| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.IntegralDatumPullCompositionReduction | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.IntegralOpenAdjunctionReduction | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.IntegralProjectionDirectFactorEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.IntegralProjectionEvaluationFactors | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.IntegralProjectionPullEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.IntegralProjectionSystemEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.IntegralProperSupportReductionIdentity | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.IntegralPublishedCounitEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.IntegralPublishedFiniteEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.IntegralPublishedTowerEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.NativeProperDerivedPresentation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.OrdinarySystemPullbackCompositorEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.ReindexingSystemHomReductionSquare | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.SystemFiniteCompositorCoordinates | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.SystemIdentityOpenEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.Paper.SystemPullbackCompositorEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralDirectEvaluationMateInvertible | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralFinitePullbackNormalization | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralNativeDerivedComparison | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralNativeDirectComparison | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralNativeOpenComparison | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralNativeOrdinaryComparison | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralNativeOrdinaryPullEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralNativePullEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralOpenFiniteEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralProperFiniteProjection | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralPullEvaluationQuotientSquare | H4 | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralReductionPullFiniteSquare | J1 | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralSystemDirectEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralSystemOpenComparisons | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralSystemOpenEvaluation | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralSystemOperationModels | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |
| Sheaf.SixFunctors.SystemProperOpenSupport | unclaimed | Unchanged coherent evaluation and coherence declarations, publicly re-exported by the construction module. |

## Status

landed 20261028T034944-L-3574173 2026-10-28 (merge of deliver/T3/Sheaf.Paper.CompletedPullbackTensorConstruction)
