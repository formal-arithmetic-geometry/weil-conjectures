## What changed

Proved `normalized_scalar_associator_localization_transport` by constructing the
source and target object equalities from the three realization equalities, applying
a strictly smaller integral transport theorem, and transporting that equality through
rationalization. Added the proof-only module
`Sheaf.Paper.NormalizedScalarAssociatorIntegralTransport` containing the one remaining
integral transport statement.

## Proved and sorry left

Closed the `sorry` in `normalized_scalar_associator_localization_transport`.
Added one strictly smaller, named `sorry` in
`normalized_scalar_associator_integral_transport`; its DAG node is
`lem-sf-normalized-scalar-associator-localization-transport-integral`.

## No longer needed

No imports were removed. The original direct proof route through the two scalar
comparison nodes is replaced in this item by the new integral transport node; those
nodes remain dependencies of that new statement and are still needed there.

## Where the brief, the DAG or earlier work was wrong

The original plan exposed the full localization transport as one obligation, while
the Lean proof naturally separates the integral heterogeneous equality from its
functorial rationalization transport. The DAG is updated with that strictly smaller
integral substep.

## New nodes

- `lem-sf-normalized-scalar-associator-localization-transport-integral`, implemented
  by `Sheaf.Paper.NormalizedScalarAssociatorIntegralTransport`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NormalizedScalarAssociatorIntegralTransport": "ca65d76b1cb4d5199e05e6248f971c09c2f03356", "Sheaf.Paper.NormalizedScalarAssociatorLocalizationTransport": "7b4206d9d8b91a66e23a9eb7a5f324b232f23bb5"}, "results": {"Sheaf.Paper.NormalizedScalarAssociatorLocalization": {"hash": "f954a50b2ed502d46823340f69ff92b29f70329e", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T01:33:33+0800", "transitive": 0, "version": 1}
```

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
