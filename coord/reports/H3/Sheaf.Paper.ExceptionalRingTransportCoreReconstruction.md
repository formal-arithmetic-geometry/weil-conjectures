## What changed

Filled `WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_reconstructions`.
The proof obtains the shift family from the split shift-witness theorem, obtains a
single-endpoint reconstruction for every field stage and endpoint, and assembles those
witnesses into `TransportCorePreData`. Added proof-only imports for the two split
modules. The item module now compiles with no `sorry`.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_reconstructions`.

Added two named `sorry` theorems, each with its own node and docstring:

- `WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_endpoint_reconstruction`,
  node `new-lem-sf-exceptional-ring-transport-endpoint-reconstruction`.
- `WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_left_shifts`,
  node `new-lem-sf-exceptional-ring-transport-left-shifts`.

No definition contains a `sorry`. This is a decomposition of the original construction
into the endpoint reconstruction and inherited-shift subarguments; the assembly proof
is complete.

## No longer needed

No imports were removed and no existing module was withdrawn. The original direct proof
route through the normalized reconstruction calculus is no longer needed in the item
module itself: it is cited by the two split node plans, which are the strictly smaller
subarguments now imported by the item. No DAG dependency is globally pruned because the
split nodes still require that calculus.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan described endpoint reconstruction and shift transport together,
while the Lean interface exposes them as independent data fields. The implementation
therefore splits those two strictly smaller obligations before assembling the parent
record. No target or existing statement was changed.

## New nodes

`new-lem-sf-exceptional-ring-transport-endpoint-reconstruction` records the one-field-stage,
one-endpoint normalized reconstruction witness and remains open with a named `sorry` in
`lean/Sheaf/Paper/ExceptionalTransportEndpointReconstruction.lean`.

`new-lem-sf-exceptional-ring-transport-left-shifts` records the inherited integer-shift
witness for the supplied left realizations and remains open with a named `sorry` in
`lean/Sheaf/Paper/ExceptionalTransportLeftShift.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingTransportCoreReconstruction": "f4d71239a5c408af93197d8db822ef4effc14990", "Sheaf.Paper.ExceptionalTransportEndpointReconstruction": "5596b992511530ac03b31e4507d88951cfd871c4", "Sheaf.Paper.ExceptionalTransportLeftShift": "c60bfd88a7f8711b3c8d88408449abf57ceeb426"}, "results": {}, "time": "2026-10-28T08:17:21+0800", "transitive": 0, "version": 1}
```

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
