## What changed

Proved `WeilConjectures.finitePartialTensor_identityNaturality` by applying the faithful
fixed-coordinate functor and cancelling the target coordinate isomorphism. The remaining
coordinate square is isolated in the new module
`Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinates`, which is imported by the
item module. Updated the item node proof dependencies to record this route.

## Proved and sorry left

Closed the `finitePartialTensor_identityNaturality` sorry. Added one named split-off
sorry, `finitePartialTensor_identityNaturality_coordinates`, in the new coordinate module;
its node is `lem-sf-finite-partial-tensor-identity-naturality-coordinates`.

## No longer needed

No imports or declared dependencies were removed. The direct proof uses only the coordinate
naturality split, faithfulness of `coordinates`, and cancellation by `targetCoordinates`.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the explicit coordinate naturality square needed after
expanding `pullbackTensorComparison`; this square is now recorded as a separate node.

## New nodes

`lem-sf-finite-partial-tensor-identity-naturality-coordinates`: coordinate-level naturality
of the finite partial tensor comparison after postcomposition with target coordinates.
The corresponding statement module is
`lean/Sheaf/Paper/FinitePartialTensorIdentityNaturalityCoordinates.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FinitePartialTensorIdentityNaturality": "d826dc4b5a1f0ab6d77145ba179d3d346aa69803", "Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinates": "39f619ecda0349b290bafdd3e1e300589980d075"}, "results": {}, "time": "2026-10-28T04:35:44+0800", "transitive": 0, "version": 1}
```

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
