# AlgebraicGeometry.generic_fibre_points_smooth

## Reason

Repair the landing return for head `d30874104`: the inherited file-level
warning-suppression command was counted as an unattributed hole by the landing
scanner. Removing this unnecessary option restores normal warnings. This changes
only a diagnostic option; the theorem's statement, public imports, notation,
instances, and every mathematical definition remain identical. Its completed
proof is retained. No downstream adaptation is necessary.

## Old

```lean
set_option autoImplicit false
set_option warn.sorry false
```

## New

```lean
set_option autoImplicit false
```

## Users

`tools/downstream.py Sheaf.TraceFormula.GenericFibrePointsSmooth --uses
AlgebraicGeometry.generic_fibre_points_smooth` lists the following 45 downstream
modules. No downstream file mentions the declaration by name. The warning option
has no effect on their statements or proofs and does not change exported data.
All users therefore keep their original sources. No consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.GenericFibrePointsSmooth | X7 | Remove warning suppression; completed proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.DvrNodalEtaleLocalForm | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalApproximationFiniteEtaModification | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | No mathematical or source change. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | No mathematical or source change. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No mathematical or source change. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No mathematical or source change. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No mathematical or source change. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.FiniteEtaModificationGluing | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ValuationNodalPolarSection | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ValuationReducedFibreNormalization | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | No mathematical or source change. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | No mathematical or source change. |

The generic-fibre smoothness theorem keeps exactly its existing signature. No
target definition changes, so no target statement review is reopened.

## Status

landed 20261023T132404-L-2264191 2026-10-23 (merge of deliver/X7/Sheaf.TraceFormula.GenericFibrePointsSmooth)
