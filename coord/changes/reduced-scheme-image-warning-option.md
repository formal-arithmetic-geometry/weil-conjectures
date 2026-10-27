# AlgebraicGeometry.schemeTheoreticImage_reduced

## Reason

Repair the return of delivery `b172034b59c`: the landing hole scanner attributed
an occurrence in the file-level `warn.sorry` option to no named theorem.
Remove that unnecessary warning-suppression command. The complete theorem proof
is retained. Preflight requires this record because it classifies a file-level
option removal as an interface-command change.

## Old

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false
```

## New

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
```

No declaration signature, definition, attribute or public import changes.
This warning option controls diagnostics while elaborating this file; it changes
neither the theorem's elaborated type nor anything used in consumer proofs.
The repaired module compiled in 3.5 seconds with no Lean diagnostics.

## Users

The table lists the item and every transitive downstream module reported by
`tools/downstream.py Sheaf.TraceFormula.ReducedSchemeImage --uses
AlgebraicGeometry.schemeTheoreticImage_reduced` on 2026-10-23. Its declaration-use
scan reports only the declaration in the item itself. No consumer source needs
adaptation because the only additional repair is removal of a diagnostic option.
Existing consumers retain the same statements and definitions; the original
proof delivery also keeps all public imports and signatures unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.ReducedSchemeImage | V7 | Warning option removed; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgClosedCurveModel | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ElementaryContractionEvaluation | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EmbeddedResolutionAmbientComparison | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FunctorialFanDesingularization | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HilbertSamuelLocalPresentations | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HilbertSamuelReachableLevels | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HilbertSamuelSmoothDimensionProfile | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.NodalContractionEulerDefect | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ResolutionInvariantCalculus | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SemilinearEquivariantChowModification | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothFunctorialNormalizedToricDesingularization | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothFunctorialOrdinaryResolution | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.StacksNodalClosedSubcurve | U1 | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.SecTraceFormula.SmoothCenterBlowupGeometry | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.CurveP1TreeLocalCriterion | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.NodalContractionNormalizationBranches | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.NodalSubcurveBoundary | F1 | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | No change to statement, definitions or proof; no adaptation needed. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | No change to statement, definitions or proof; no adaptation needed. |

## Status

landed 20261023T132030-L-2186174 2026-10-23 (merge of deliver/V7/Sheaf.TraceFormula.ReducedSchemeImage)
