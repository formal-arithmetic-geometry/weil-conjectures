# rationalHomScalar_transpose import dependencies

## Reason

The proof of `scalarEvaluation_of_normalizedCounits` needs the existing
`rationalHomScalar_transpose` theorem. Its module unnecessarily publicly imports
`Sheaf.SixFunctors.RationalOperations`, which now proves its Hom clause through
`RationalHomIdentifications`, `RationalHomScalarEvaluation`, and this item.
Importing the transpose theorem therefore creates an import cycle.

The transpose statement uses only the rational tensor, scalar extension, partial
closed structure, and their comparisons already supplied by its other imports.
It uses no declaration from the rational-operations identification theorem or
its data interface. Remove the unused import and the corresponding stale
`lem-coef-rational-operations` statement-dependency edge in the transpose node.
The theorem statement, body, attributes, and remaining imports are unchanged.
The transpose module is unclaimed in the shared claim snapshot.

## Old

The public import block of `Sheaf.Paper.RationalHomScalarTranspose`:

```lean
public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.SixFunctors.RationalOperations
public import Sheaf.Paper.CompletedTensorHomTranspose
public import Sheaf.Paper.SitePerfectComplex
```

The node `lem-coef-rational-hom-scalar-transpose` additionally lists
`lem-coef-rational-operations` in `stmt_deps`.

## New

```lean
public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.Paper.CompletedTensorHomTranspose
public import Sheaf.Paper.SitePerfectComplex
```

Remove only `lem-coef-rational-operations` from that node's `stmt_deps`.
All declarations retain their exact signatures and bodies. No target meaning
or shared definition changes.

## Users

`tools/downstream.py Sheaf.Paper.RationalHomScalarTranspose --uses
rationalHomScalar_transpose` reports exactly the two existing direct importers
below (and the declaration's own module as a textual use). Both imports are
private, so no existing module publicly re-exports the removed import through
this module. The new importer is the assigned item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed in shared snapshot | Remove one unused public import; declaration unchanged. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed in shared snapshot | Uses the unchanged transpose theorem; compiled unchanged against the pruned import. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed in shared snapshot | Already directly imports RationalOperations; compiled unchanged. |
| Sheaf.SixFunctors.RationalHomScalarEvaluationCore | A4 | New proof-only importer; proves the assigned evaluation square. |

## Status

landed 20261028T055601-L-769325 2026-10-28 (merge of deliver/A4/Sheaf.SixFunctors.RationalHomScalarEvaluationCore)
