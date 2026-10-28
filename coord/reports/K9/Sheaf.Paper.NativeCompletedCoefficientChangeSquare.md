## What changed

Added the proof-only import `Sheaf.Paper.NativeCompletedCoefficientIntegralMapSquare`.
The assigned theorem now introduces `U`, `V`, and `g`, rewrites `m U` and `m V`
with `hC`, and applies the explicit integral-map square theorem.
The new theorem is stated in its own module with the finite-quotient proof obligation.

## Proved and sorry left

Closed the original `sorry` in
`native_completed_coefficient_change_square_of_presentation`.
Added one strictly smaller split obligation,
`coefficient_presentation_integralMap_pull_square`, at node
`lem-sf-native-completed-coefficient-integral-map-square`.

## No longer needed

None. The assigned module's original public import remains necessary, and the new
proof-only import is used by the proof.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan omitted the explicit integral-map square as a separate
Lean statement. The assigned theorem is a wrapper around that square once `hC` is
rewritten; the missing cross-scheme calculation is recorded as the new node.

## New nodes

`lem-sf-native-completed-coefficient-integral-map-square` is implemented by
`Sheaf.Paper.NativeCompletedCoefficientIntegralMapSquare` and declares
`coefficient_presentation_integralMap_pull_square`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeCompletedCoefficientChangeSquare": "459bbd30e40da1175201ca24fce5de7756276b92", "Sheaf.Paper.NativeCompletedCoefficientIntegralMapSquare": "25285f08d51daa8b46db41ee746d0aeb9f617d32"}, "results": {}, "time": "2026-10-28T07:59:54+0800", "transitive": 0, "version": 1}
```

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
