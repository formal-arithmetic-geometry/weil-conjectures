# stage3-pur-normalized-scalar-tower-comparisons

## Reason

Its proof record cited the broad completed comparison node, whose proof now uses this item.
The actual Lean source already imports the self-contained integral constructor instead. This
stale DAG citation introduces an artificial proof cycle when the scalar coordinate lemma uses
the existing scalar pullback limit square. Correct the record to match the existing Lean proof.
No Lean source, signature, statement, definition, import or attribute changes in this module.

## Old

The proof step and proof_deps of `stage3-pur-normalized-scalar-tower-comparisons` include
`def-pur-completed-pullback-tensor-comparison`.

## New

Replace that dependency by `def-pur-completed-pullback-tensor-integral-construction`.
`ScalarExtensionTowerComparisonData.lean` already privately imports
`CompletedPullbackTensorIntegralConstruction`; lines 480–488 use the proved private theorem
`pullbackTensorSequenceRing_eq` and the preexisting `pullbackTensorSequenceCochain_existsUnique`.
There is no use of the completed scalar compatibility theorem or its containing construction
module. The proof text and proof_origin explain this precision. No other node fields change.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarExtensionTowerComparisonData | unchanged, no adaptation | Its DAG proof dependencies now reflect its existing Lean proof. |
| Sheaf.Paper.ScalarTowerPullbackStrictSquare | unchanged, no adaptation | Existing proved dependency on normalized comparison data; no Lean change. |
| Sheaf.Paper.CompletedScalarRouteCoordinates | H9, new | Its limit-square proof route avoids the stale circular citation. |
| Sheaf.Paper.CompletedComparisonScalarLimitImage | H9 | Uses the new coordinate lemma after the dependency-record correction. |

All Lean consumers see identical declarations and public imports; no consumer needs adaptation.
Only the proof route record changes, so no target statement or definition is reopened.

## Status

landed 20261028T081743-L-2778614 2026-10-28 (merge of deliver/H9/Sheaf.Paper.CompletedComparisonScalarLimitImage)
