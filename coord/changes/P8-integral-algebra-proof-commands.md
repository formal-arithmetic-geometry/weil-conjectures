# AlgebraicGeometry.integral_algebra_directed_colimit_finite

## Reason

The proof uses opposite-open notation, an underlying module functor, and explicit affine
section morphisms. Added `Opposite TopologicalSpace` to the local open namespaces and
`backward.isDefEq.respectTransparency false` for elaboration of the existing aliases
`Scheme.Modules`, `SheafOfModules`, and `TopCat.Sheaf`. The original statement's second
existential isomorphism binder is unused in its proposition, so its existing warning is
suppressed by `set_option linter.unusedVariables false in` scoped to this theorem.
The static interface checker asks for a record for these commands. No public declaration
type, definition, instance, attribute, or public import changes. Private helpers are proved.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

There was no local elaboration-option override and no scoped linter suppression.
The original theorem signature is kept verbatim in the delivered file.

## New

```lean
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
```

Immediately before the theorem docstring:

```lean
set_option linter.unusedVariables false in
```

These commands affect elaboration of this file only. Its theorem signature and public
imports are byte-for-byte the same. All added proof imports are private.

## Users

Computed using `python3 tools/downstream.py Sheaf.AlgebraicGeometry.IntegralAlgebraDirectedColimitFinite --uses
integral_algebra_directed_colimit_finite`. The only textual reference to the declaration
is its own declaration; the 49 downstream modules below see precisely its previous type.
The three direct importers are IntegralLisseClosedBaseChange,
IntegralHenselianLisseSectionRigidity, and FiniteEtaModificationGluing; quarantined copies
of these direct importers likewise need no edits. No other module is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralFibreSectionSpecialization | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralHenselianLisseSectionRigidity | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralLisseClosedBaseChange | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.Paper.KummerPartialNerveNaturality | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.FiniteEtaModificationGluing | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | Statement and public imports unchanged; no adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | Statement and public imports unchanged; no adaptation. |

## Status

landed 20261023T124025-L-1312397 2026-10-23 (merge of deliver/P8/Sheaf.AlgebraicGeometry.IntegralAlgebraDirectedColimitFinite)
