## What changed

Proved `WeilConjectures.finitePartialTensor_identityComponent` by applying the faithful
fixed-coefficient coordinate functor, cancelling the final target coordinate isomorphism,
and invoking the fixed-coordinate identity-composition square. Added the named lower
coordinate square `finitePartialTensor_identityComponent_coordinates`, whose proof is the
remaining fixed-coefficient expansion and is left for a subsequent worker.

## Proved and sorry left

- Closed the `sorry` in `WeilConjectures.finitePartialTensor_identityComponent`.
- Added one strictly lower, fixed-coordinate theorem with a `sorry`:
  `WeilConjectures.finitePartialTensor_identityComponent_coordinates`.
- No definition contains `sorry`.

## No longer needed

The proof uses `FinitePullbackTensorFixedCoordinates` through the new coordinate module;
there were no unused imports or proof-dependency nodes to prune.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery only added the fixed-coefficient identity specialization while leaving
the realization-level component theorem open. The missing reduction is faithfulness of the
coordinate functor followed by cancellation of `targetCoordinates`; this is now explicit in
the item proof and in the new lower node.

## New nodes

- `lem-sf-finite-partial-tensor-identity-fixed-coordinates`, realized by
  `Sheaf.Paper.FinitePartialTensorIdentityComponentCoordinates`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FinitePartialTensorIdentityComponent": "5e3d6262bb4b8e51348d592a5e5293b10fe5b0d4", "Sheaf.Paper.FinitePartialTensorIdentityComponentCoordinates": "9df6c5994303bbb53ab144f0160408a0b2a0f93e"}, "results": {}, "time": "2026-10-28T05:23:31+0800", "transitive": 0, "version": 1}
```

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
