## What changed

Proved `integral_support_adjoint_of_preservation` after removing the cyclic import of
`ExceptionalRingOperationsExistence`. The proof instantiates a new, strictly simpler integral
operation/realization statement at `RingStage.integral E`, transports its operation adjunction
through the compact-support `LeftRealization`, and uses the resulting object-property natural
isomorphism to the canonical lift defined by `hpres`. The proof uses
`AlgebraicClosure (ULift (Padic l))` to match the datum universe.

## Proved and sorry left

The item theorem is proved and contains zero `sorry`s. One strictly simpler theorem was split off:
`exists_integral_support_operation_realization` in
`Sheaf.Paper.IntegralSupportOperationRealization`; its proof remains `sorry` for a later worker.

## No longer needed

The planned imports `Sheaf.Paper.IntegralSupportPreservation`,
`Sheaf.Paper.ExceptionalSystemTransport`, and
`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` are not needed by the item proof.
`Sheaf.Paper.ExceptionalRingOperationsExistence` is also not imported because it imports the
parent `ExceptionalIntegralSupportAdjoint` and creates a cycle.

## Where the brief, the DAG or earlier work was wrong

The prior route through `ExceptionalRingOperationsExistence` was invalid: that module imports
`ExceptionalIntegralSupportAdjoint`, whose proof imports this item. The operation-family theorem
therefore cannot be used from this module. The replacement split records only the integral-stage
operation and realization required by the transport, and has an acyclic `Data` import.

## New nodes

`lem-sf-integral-support-operation-realization` records existence of the integral operation and
its compact-support left realization. It is strictly simpler than the item theorem because it
does not quantify over an arbitrary preservation witness or conclude `IsLeftAdjoint` for the
canonical lift.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralSupportAdjointOfPreservation": "1ff7c99dc493f4e7e9ee0b5b14ef332d264b446c", "Sheaf.Paper.IntegralSupportOperationRealization": "4df9da21d7eb301fa52df7f924c0707060f89311"}, "results": {}, "time": "2026-10-28T07:43:06+0800", "transitive": 0, "version": 1}
```

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
