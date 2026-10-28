## What changed

Inspected the existing `restrictionTensor_transition` theorem and its dependencies. The
module retains the existing named `sorry`; its docstring now records the mathematical
issue found with the statement.

## Proved and sorry left

No holes were closed. `WeilConjectures.IntegralHom.restrictionTensor_transition` remains a
single named `sorry` (node `lem-sf-integral-tensor-restriction-transition`).

## No longer needed

No imports or DAG dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The displayed conclusion quantifies over an arbitrary family
`m : ∀ n, ReductionPresentation ... a n`. A `ReductionPresentation` contains a target
presentation and a tensor comparison `mu` at one level, together with a normalization
condition, but it contains no compatibility datum relating `m n` to `m (n+1)` or their
target tensor presentations. The two sides of the claimed equality use those unrelated
choices. The representative calculation described in the proof would establish the
square only for a coherently chosen tower of presentations, or after adding an explicit
compatibility hypothesis. Consequently the current statement is underdetermined and is
marked `STATEMENT-DISPUTED` in the module; proving it would require silently adding a
hypothesis.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralTensorRestrictionTransition": "96882674393085ef6e2028c4717fa21959eec1d6"}, "results": {}, "time": "2026-10-28T10:37:52+0800", "transitive": 0, "version": 1}
```

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
