## What changed

Marked `scalarIdentityNormalizationAtClosure` as `STATEMENT-DISPUTED`. The theorem
quantifies over an arbitrary natural isomorphism `J`, while the available certificate
`I.normalized` proves the equation only for `I.iso` (transported through the finite or
integral presentation). No proof body was changed.

## Proved and sorry left

No holes were closed. The existing hole in
`scalarIdentityNormalizationAtClosure` remains, at
`dag/nodes/sec-six-functors/lem-sf-ring-endpoint-scalar-identity-normalization-transport.json`.
No new holes were added.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The statement's arbitrary `J` is stronger than the normalization data supplied by `I`.
There is no subsingleton or uniqueness principle for natural isomorphisms between the
scalar functor and the identity, so `J` cannot be replaced by `I.iso`. Lean reports the
mismatch directly when applying `I.normalized K`. The intended statement must constrain
`J` to the canonical transported isomorphism (or include an equivalent compatibility
hypothesis).

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RingEndpointScalarIdentityNormalization": "2471e4e009d66150cd52f7c651b8bfc6cf877e4c"}, "results": {}, "time": "2026-10-28T11:23:06+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
