## What changed

The target theorem now assembles two chain-level comparison steps.  The first
split-off theorem supplies a strict scalar pullback cone and a normalized
invertible map on the good-complex subcategory.  The second split-off theorem
transports the cone's finite-coordinate normalization through the completed
inverse limit.  The target proof combines these declarations and contains no
`sorry`.

## Proved and sorry left

Closed the `scalar_completed_formula` hole.  Two strictly smaller intermediate
theorems remain as named obligations:

* `completed_formula_chain_data` in
  `Sheaf.Paper.IsomorphismScalarCompletedFormulaChainData`.
* `completed_formula_chain_normalization` in
  `Sheaf.Paper.IsomorphismScalarCompletedFormulaChainNormalization`.

## No longer needed

None.  The target retains its vocabulary import and adds only the two modules
containing the chain-level steps used by its proof.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the strict cone construction, invertibility on
the good subcategory, and inverse-limit section calculation as one direct
specialization of `limitScalarChainComparison`.  The published declarations
expose these as separate chain-level interfaces, so the direct specialization
cannot be written without first stating the two intermediate comparison steps.
The target statement itself is unchanged.

## New nodes

* `lem-weil-isomorphism-scalar-completed-formula-chain-data`
* `lem-weil-isomorphism-scalar-completed-formula-chain-normalization`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarCompletedFormulaChainData": "19d927e8d7465b44b1b913a23d3eec4b78afda7e", "Sheaf.Paper.IsomorphismScalarCompletedFormulaChainNormalization": "8ffcfa3aa54ddd53618102b4d38d20c29e50d7cd", "Sheaf.Paper.IsomorphismScalarCompletedModelFormula": "90f62f969bbc726292f80c33796f6ee06f1f4c63"}, "results": {}, "time": "2026-10-28T08:11:25+0800", "transitive": 0, "version": 1}
```

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
