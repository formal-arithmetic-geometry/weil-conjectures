## What changed

Added `Sheaf.TraceFormula.NestedChosenScalarTensorValExt`, which states the underlying-sheaf tensor-induction substep and imports it in the assigned module. The assigned theorem now applies this substep and finishes with `SheafOfModules.hom_ext`.

## Proved and sorry left

The assigned theorem `completedNestedScalarTensor_ext` is proved. One strictly lower substep remains as the named theorem `nestedChosenScalarTensor_val_ext` (blueprint `lem-trf-nested-chosen-scalar-tensor-val-ext`).

## No longer needed

No imports or declared dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The source module's private tensor extensionality helper is not exported, so the nested statement requires an explicit underlying-sheaf tensor-induction substep.

## New nodes

`lem-trf-nested-chosen-scalar-tensor-val-ext` records the remaining underlying-sheaf tensor-induction theorem in `Sheaf.TraceFormula.NestedChosenScalarTensorValExt`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.TraceFormula.NestedChosenScalarTensorValExt": "8d26c8526dc80899a1aaba2ab64c9f5900ad2298", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateComponentExtensionality": "95d0f060abac7786785955c46603aa2557d103d3"}, "results": {}, "time": "2026-10-28T08:31:21+0800", "transitive": 0, "version": 1}
```

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
