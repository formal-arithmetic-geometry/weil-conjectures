# AlgebraicGeometry.perfect_local_models_descended_transition

## Reason

Restore the assigned zero-hole rework item from its preserved quarantine source.
The old public import names a withdrawn empty Sheaf module. The archived source
fails with five `Unknown identifier derivedPullback` errors (lines 106, 108, 128,
129 and 154); Lean identifies the public owner as
`WeilConjectures.AlgebraicGeometry.DerivedPullback`.
The actual repair imports that owner publicly, as required by the theorem statement.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

The remainder of the archived module, including its single theorem's signature,
proof, docstring, local instances, options and two proof imports, is byte-identical.
No definition or target meaning changes. The canonical derived pullback is the
same adopted declaration already used by the comparison-diagram dependency.
The existing DAG attachment and all dependencies are preserved verbatim.

## Users

`tools/downstream.py --allow-missing --uses` reports no live consumers because
this item and its parent are quarantined. A separate source scan over the archive,
overlaid by live sources, finds the direct importer
`Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons` and 36 transitive
consumers. Its call at archived line 188 uses exactly the preserved theorem type.
The table includes the full conservative archive/live closure and current holders.
There are no forced consumer adaptations; the archived parent separately has its
own obsolete Sheaf DerivedPullback import, which this restoration does not change.
A fresh importing module checks application of the theorem at the entire verbatim
archived type; this checks public visibility as well as the consumer-facing API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition | E1 | Restored item; theorem signature and proof unchanged. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Same theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Same theorem API; no adaptation. |

## Status

landed 20261023T041808-L-1695575 2026-10-23 (merge of deliver/E1/Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition)
