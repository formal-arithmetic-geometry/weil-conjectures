## What changed
Added `Sheaf.Paper.GabberCriterionDegree` with the fixed-degree intermediate theorem and reduced `gabberCriterion` to it.

## Proved and sorry left
`gabberCriterion` is proved by applying `gabberCriterion_degree` for each positive degree. `gabberCriterion_degree` remains a named sorry split at node `lem-weil-pbc-gabber-criterion-degree`.

## No longer needed
The parent proof no longer directly uses its original proof dependencies; they are encapsulated by the fixed-degree split.

## Where the brief, the DAG or earlier work was wrong
The original proof plan is too large to formalize in the allotted session; it was split at the fixed-degree induction theorem.

## New nodes
`lem-weil-pbc-gabber-criterion-degree` in `dag/nodes/sec-proper-base-change/lem-weil-pbc-gabber-criterion-degree.json`.

## Earlier second reading (a previous round; superseded)
The reduction applies the fixed-degree statement pointwise and preserves the target statement exactly; the new fixed-degree node is a strict induction component.

## Second reading by F1

1. **Statements unchanged.** I diffed `GabberCriterion.lean` against the repository version. The `gabberCriterion` signature is byte-for-byte unchanged; only a proof-only import and proof body were added. The fixed-degree statement is the original conclusion specialized to an explicit positive `q`, with no weakened hypotheses or conclusion.
2. **Proof checks.** Both modules compile with `lcompile.py --all`. The only remaining `sorry` is the named theorem `gabberCriterion_degree`, and it has the matching split node and source/docstring. No forbidden declarations occur. The parent proof is a direct application for arbitrary positive `q`.
3. **Split statement review.** `gabberCriterion_degree` is true as the fixed-degree component needed by the parent and is not a restatement of the parent because it exposes one fixed degree; no existing library or Mathlib declaration duplicates it. Its node records the Stacks source and proof route.
4. **Pruning and route.** The parent now uses only `lem-weil-pbc-gabber-criterion-degree`; the original induction dependencies remain in that split theorem's node/module. The unit `sk-thm-p1` route and its `realized` fields are untouched.
5. **DAG agreement.** Updated the parent node's `proof`, `proof_deps`, and `proof_origin` to match the Lean proof, and retained the complete node for the split theorem.

Changed in this second reading: synchronized the parent DAG node with the proof and added this review record.
