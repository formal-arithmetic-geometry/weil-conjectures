## What changed

Added the lower good-localization scalar comparison theorem as a separate module and
used it to close the ambient realization theorem by the existing scalar-extension
localization universal property. The target proof now extracts the descended functor
from `integralScalarExtensionWellDefined` and returns its comparison isomorphism.

## Proved and sorry left

Closed `ambientQuotientScalarModel_realization_exists` (1 of 1 original sorries).
Added one strictly lower construction statement, with its proof left as `sorry`:
`ambientQuotientScalarModel_good_comparison`.

## No longer needed

No imports or declared dependencies were removed. The target proof uses only the
realization-model definitions, the scalar sequence functor, the scalar good tower,
and the new good-localization comparison; the normalization theorem is not needed
for this realization-only item.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original proof step omitted the explicit
localization descent interface; the delivery records it as a separate lower node.

## New nodes

`new-trf-ambient-quotient-scalar-good-comparison` owns the balanced scalar comparison
on the flat-term K-flat localization. Its statement is strictly below the target:
it compares the restriction of the candidate functor to the good localization before
constructing the ambient derived-category realization.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AmbientQuotientScalarGoodComparison": "e275733a7f6e23e56d7d1c75134cb071e92edbca", "Sheaf.Paper.AmbientQuotientScalarRealizationExistence": "8cfc0eecbcb5d8dc02e64bf255a55832b4c718ab"}, "results": {}, "time": "2026-10-28T05:18:27+0800", "transitive": 0, "version": 1}
```

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
