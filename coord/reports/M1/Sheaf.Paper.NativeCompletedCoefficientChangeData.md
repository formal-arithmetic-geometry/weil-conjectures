## What changed

Reduced `native_completed_coefficient_change_data` to two named construction steps and proved the original theorem by composing them. The presentation-family and pullback-square steps are recorded as separate statement modules with their own DAG nodes.

## Proved and sorry left

Proved `native_completed_coefficient_change_data` (1 original sorry closed). Added the strictly simpler statement-only obligations `exists_native_completed_coefficient_presentation` and `native_completed_coefficient_change_square_of_presentation` (2 sorries split off).

## No longer needed

No imports or declared dependencies were pruned; the original construction dependencies remain the basis of the two split-off steps.

## Where the brief, the DAG or earlier work was wrong

The original node bundled presentation existence, normalization, and pullback compatibility into one theorem, while the available interface exposes these as independent construction obligations. The node proof is updated to reflect the two-step reduction.

## New nodes

- `lem-sf-native-completed-coefficient-change-presentation`
- `lem-sf-native-completed-coefficient-change-square`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeCompletedCoefficientChangeData": "5d754fa3b5c08dcca70c03636160f513b241ce52", "Sheaf.Paper.NativeCompletedCoefficientChangePresentation": "e901bcd70536c06cdaf7756ce2450c858b2cd242", "Sheaf.Paper.NativeCompletedCoefficientChangeSquare": "6969ae1c9ce6c634ee41d37bf4ea286e30ed5927"}, "results": {}, "time": "2026-10-28T06:47:44+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
