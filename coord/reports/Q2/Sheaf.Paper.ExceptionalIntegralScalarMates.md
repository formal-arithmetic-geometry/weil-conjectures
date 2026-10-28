## What changed

Added the strictly smaller pointwise theorem
`exceptionalIntegralScalarMates_data_reduction_pointwise` to isolate the construction of one
`ReductionMates` record at a fixed field stage and level. The quantified
`exceptionalIntegralScalarMates_data_reduction` theorem now has a complete proof by choosing the
pointwise records. Added the matching DAG node
`lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise`.

## Proved and sorry left

Closed `exceptionalIntegralScalarMates_data_reduction` (one sorry). The item still has these
named construction obligations as sorry:

- `exceptionalIntegralScalarMates_data_mates` (the existing node
  `lem-sf-exceptional-integral-scalar-mates-data-mates`).
- `exceptionalIntegralScalarMates_data_reduction_pointwise` (new node
  `lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise`).
- `exceptionalIntegralScalarMates_system` (the existing node
  `lem-sf-exceptional-integral-scalar-mates-system`).

The module therefore has three sorry declarations after the decomposition and one upper hole
closed.

## No longer needed

No imports or existing proof-dependency nodes were removed. The quantified reduction theorem now
uses only the new pointwise declaration in its Lean proof; the pointwise declaration retains the
three construction dependencies listed in its DAG node.

## Where the brief, the DAG or earlier work was wrong

The earlier split left a quantified `Nonempty (∀ E n, ReductionMates ...)` as a direct sorry even
though its logical assembly from pointwise records is elementary. The actual mathematical
construction remains the new pointwise obligation; no statement was weakened.

## New nodes

`lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise` records the fixed-`E`, fixed-`n`
reduction construction and its source, proof step, searches, and Lean declaration.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalIntegralScalarMates": "65f318544035d66081f93ce86402e817a1111f7e"}, "results": {"Sheaf.Paper.ExceptionalRingOperationsExistence": {"hash": "12b6f37c3f38af79a030a433dc2ffb6b444cf31b", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCore": {"hash": "87222536a47dc08a48ed436e6a8378b42f61ec3c", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreReconstruction": {"hash": "97117b29062089e316f192d7e9687762f18e2ced", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportFamily": {"hash": "5960d42c061d3c3d87bda0f357d5137c36100426", "status": "OK"}}, "seconds": 131, "time": "2026-10-28T07:48:32+0800", "transitive": 0, "version": 1}
```

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
