# def-pod-scalar-completion-tensor-comparisons

## Reason

This definition cites the completed pullback/tensor comparison as its source of completed
tensor. That operation is defined independently in def-pur-integral-derived-operations.
Neither scalarCompletion nor scalarTensorOrdinary uses the completed pullback/tensor comparison
or its scalar compatibility theorem. The mistaken citation creates a spurious DAG cycle.

## Old

The statement's first sentence says:
“For prime $\\ell$, finite $E,L/\\mathbf Q_\\ell$, an embedding $\\iota:E\\to L$ and scheme $W$, use ordinary derived scalar extension and completed tensor [def-weil-integral-scalar-extension] [def-pur-completed-pullback-tensor-comparison].”
The stmt_deps are def-weil-integral-scalar-extension and
def-pur-completed-pullback-tensor-comparison. The node's statement_change.old_statement and
old_stmt_deps preserve the complete originals verbatim.

## New

Replace only the completed tensor citation by def-pur-integral-derived-operations, both in
that sentence and in stmt_deps. All other words, all Lean signatures and both actual definitions
are unchanged. IntegralOperationsScalarComparisons.lean defines the maps using the existing
operation representative comparisons, scalar completion chain and ordinary tensor chain, and
imports neither CompletedPullbackTensorComparison nor CompletedPullbackTensorConstruction.
The node carries a statement_change recording every direct citer and why it remains valid.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unchanged, no adaptation | Same scalarCompletion and scalarTensorOrdinary definitions; corrected DAG citation only. |
| Sheaf.Paper.ScalarPullbackRightRoosNormalization | unchanged, no adaptation | Same completion map in its normalization equation. |
| Sheaf.Paper.CompletedComparisonScalarLimitImage | H9 | Existing limit-coordinate route has no artificial dependency on this conclusion. |

Every direct DAG citer is individually listed as holds=true in statement_change.citers.
No Lean name, signature or definition changes, so all consumer sources remain unchanged.
No target meaning changes.

## Status

landed 20261028T081743-L-2778614 2026-10-28 (merge of deliver/H9/Sheaf.Paper.CompletedComparisonScalarLimitImage)
