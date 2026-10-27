## What changed

Proved `scalarModelRoosZeroLift_nestedCoordinate_extensionality` by reducing equality of
strict first Roos coordinates to equality in every product coordinate, then applying a
new module level nested tensor extensionality theorem. Added
`ScalarModelRoosZeroLiftNestedCoordinateComponentExtensionality` as the strictly smaller
module level tensor and sheafification step.

## Proved and sorry left

Closed `scalarModelRoosZeroLift_nestedCoordinate_extensionality` (1 sorry). Added one
strictly smaller theorem, `completedNestedScalarTensor_ext`, with 1 sorry for the
module-level tensor-balancing and sheafification argument.

## No longer needed

No imports or declared proof dependencies were removed. The original direct dependency on
the full realization-model construction is retained by the new component theorem.

## Where the brief, the DAG or earlier work was wrong

The original DAG treated the nested tensor-balancing argument as a single step inside the
Roos-coordinate theorem. It is a separate module-level extensionality statement, so the
DAG was refined with that strict substep.

## New nodes

`lem-trf-scalar-model-roos-zero-lift-nested-coordinate-component-extensionality` records
`completedNestedScalarTensor_ext` and its remaining tensor/sheafification proof.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateComponentExtensionality": "940659c544635ba4946fc77f2f911c9f1e2c4833", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateExtensionality": "1080b452171d7e785b70eb73bf61cc239a41aa56"}, "results": {"Sheaf.TraceFormula.ScalarModelRoosZeroLiftUniqueness": {"hash": "b1a0b7601e311688676ecc488a5c201538f54323", "status": "OK"}}, "seconds": 34, "time": "2026-10-28T05:18:39+0800", "transitive": 0, "version": 1}
```

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
