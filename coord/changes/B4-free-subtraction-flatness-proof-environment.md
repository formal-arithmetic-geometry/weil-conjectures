# Sheaf.RingTheory.FreeSubtractionFlatness proof environment

## Reason

The completed proof adds explicit universe declarations and local commands needed by its private helpers. Preflight requires a change record for these commands even though the public theorem signature and public imports are unchanged.

## Old

```lean
@[expose] public section

universe u v w

open AlgebraicGeometry TensorProduct
```

## New

```lean
@[expose] public section

set_option autoImplicit false

universe u v w z t

open AlgebraicGeometry TensorProduct CategoryTheory
```

These commands support only private proof helpers. The public declaration `Module.free_subtraction_flatness` keeps the same signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.FreeSubtractionFlatness | B4 | Uses the explicit proof environment. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EquivariantFlatCurvePreparation | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAfterBlowup | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatteningModuleByAdmissibleBlowup | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.FiniteEtaFlatification | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | Unchanged theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | Unchanged theorem signature and public imports; no adaptation. |

`tools/downstream.py --uses free_subtraction_flatness` finds only the defining module using the declaration name; the table includes all 49 modules in the import closure as well. No target definition or statement changes.

## Status

landed 20261023T131301-L-2078455 2026-10-23 (merge of deliver/B4/Sheaf.RingTheory.FreeSubtractionFlatness)
