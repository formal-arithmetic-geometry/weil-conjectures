## What changed

The parent theorem `compactSupportQuotient_computation_squares` is proved by combining two
strictly simpler comparison-square theorems. The left and right squares are stated in
`CompactSupportQuotientComputationSquareLeft.lean` and
`CompactSupportQuotientComputationSquareRight.lean`; each remains a named split theorem
for the corresponding universal counit/adjunction calculation. The parent imports both
modules and applies their conclusions.

## Proved and sorry left

The original parent declaration `WeilConjectures.compactSupportQuotient_computation_squares`
is proved. Two strictly smaller split declarations remain with `sorry`:

- `WeilConjectures.compactSupportQuotient_computation_square_left`, node
  `lem-coef-compact-support-quotient-computation-square-left`;
- `WeilConjectures.compactSupportQuotient_computation_square_right`, node
  `lem-coef-compact-support-quotient-computation-square-right`.

This is a decomposition of the two displayed conjuncts into independently provable
universal comparison squares.

## No longer needed

No proof dependency from the original plan is removed globally. The parent proof uses
only the two split comparison-square declarations; the original direct categorical
lemmas are retained as dependencies of those split nodes. No existing declaration is
withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original two-step proof plan was mathematically sound but too coarse for a direct
Lean proof: neither universal derived comparison square is available as a single
library theorem. Splitting the conjuncts gives strictly smaller statements while
preserving the target statement and the unit route.

## New nodes

`lem-coef-compact-support-quotient-computation-square-left` and
`lem-coef-compact-support-quotient-computation-square-right` are the two split universal
comparison-square statements. Their Lean modules and node records are included in this
delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportQuotientComputationSquareLeft": "3880f849ffbdf1bb93aba908db424eda09700a62", "Sheaf.Paper.CompactSupportQuotientComputationSquareRight": "0de7502946135bc0f3b7b5fbb8d18d25b803e1e4", "Sheaf.Paper.CompactSupportQuotientComputationSquares": "ce9690302b12a9ad7be404de7d8ffa7b5eed4015"}, "results": {}, "time": "2026-10-27T23:45:24+0800", "transitive": 0, "version": 1}
```

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
