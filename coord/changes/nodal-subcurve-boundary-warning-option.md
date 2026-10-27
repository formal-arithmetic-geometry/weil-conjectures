# AlgebraicGeometry.nodal_subcurve_boundary

## Reason

Repair return fcca1ddba: the source hole ledger reads the option identifier in
`set_option warn.sorry false` as an unattributed hole. Remove this unnecessary
warning suppression now that all proofs in the item are complete. The preflight
interface comparison treats the removal of this command as an interface change,
so this record inventories its consumers. No declaration type, visibility, target
statement, public import, or mathematical definition changes.

## Old

The removed command, verbatim:

```lean
set_option warn.sorry false
```

The three public complement/boundary definitions and the theorem signature are
identical to the repository versions.

## New

The warning-suppression command is absent. The surrounding options remain:

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
```

The retained packet proves the original theorem using private helpers and private
proof imports. Its new public coefficient-straightening theorem is in
`Sheaf.RingTheory.NodalCoefficientStraightening` and has its own DAG node. No
existing signature or definition changes.

## Users

Inventory from `tools/downstream.py Sheaf.TraceFormula.NodalSubcurveBoundary
--uses nodal_subcurve_boundary`. The only textual use of the theorem name is its
own declaration; the remaining modules import it directly or transitively.
The removed option affects warnings within this file and has no mathematical
effect on these modules. No consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.NodalSubcurveBoundary | F1 | Proof completed; warning suppression removed; signature unchanged. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.ElementaryContractionEvaluation | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.NodalContractionEulerDefect | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.TraceFormula.CurveP1TreeLocalCriterion | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.TraceFormula.NodalContractionNormalizationBranches | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | No adaptation: statements, definitions, and imported declarations unchanged. |

## Status

landed 20261023T151836-L-416702 2026-10-23 (merge of deliver/F1/Sheaf.TraceFormula.NodalSubcurveBoundary)
source hole scanner finds no holes or warnings. Awaiting independent review and
the maintainer's global build.
