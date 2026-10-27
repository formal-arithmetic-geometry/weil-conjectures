## What changed

Added `Sheaf.Paper.RestrictionTensorRepresentativeStageTransport`, whose single
stage-level theorem isolates the mixed scalar-square calculation.  The assigned
module imports it and proves `restrictionTensorRepresentativeTransport` by applying
that stage identity and `StageSystem.PairCategory.mkHom_tr`.

## Proved and sorry left

The assigned theorem `WeilConjectures.restrictionTensorRepresentativeTransport` is
proved.  One strictly smaller statement remains as the named theorem
`WeilConjectures.restrictionTensorRepresentativeStageTransport` in its new module;
its proof is `sorry` and is recorded by node
`lem-pur-restriction-tensor-representative-stage-transport`.

## No longer needed

The parent proof's direct use of the scalar-extension and scalar-tower nodes is
reduced to the new stage-transport node.  No additional imports beyond
`Sheaf.Paper.DerivedPullbackTensorHom` and the new stage-transport module are
needed by the assigned module.

## Where the brief, the DAG or earlier work was wrong

The DAG described the component calculation only as prose and did not provide a
Lean statement for the stage-level transition equality.  The quotient-category
part is elementary once that equality is stated, so it is split off as the new
strictly smaller node above.

## New nodes

`lem-pur-restriction-tensor-representative-stage-transport` states the finite-stage
transport equality and is implemented by
`lean/Sheaf/Paper/RestrictionTensorRepresentativeStageTransport.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RestrictionTensorRepresentativeStageTransport": "70ff5ac439ec857220dad745b80f562f1f475c03", "Sheaf.Paper.RestrictionTensorRepresentativeTransport": "4af5c650e22ec798cf7c3c9b5a5db990f11edbe6"}, "results": {}, "time": "2026-10-28T04:28:31+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
