## What changed

Moved the explicit universe-reindexed `scalarAtClosure` construction into
`Sheaf.Paper.RingEndpointScalarIdentityTransferData`, preserving its finite/integral
case split and all five scalar fields. The assigned module now constructs the low-universe
identity isomorphism from the high-universe certificate and applies the named normalization
transport theorem. Added `Sheaf.Paper.RingEndpointScalarIdentityNormalization`, whose
single theorem isolates the normalization equation that remains to be proved.

## Proved and sorry left

The assigned theorem `scalarIdentityAtClosure` is proved from the supplied identity
certificate, the explicit `scalarAtClosure` definition, and the normalization transport
statement. One sorry remains in the split theorem
`scalarIdentityNormalizationAtClosure` in
`Sheaf.Paper.RingEndpointScalarIdentityNormalization`; it is the normalization equation
transport after the finite/integral case split. No sorry occurs in a definition.

## No longer needed

The proof no longer needs the separate public helper declarations
`scalarFunctorAtClosure`, `scalarRealizationAtClosure`, `scalarCommShiftAtClosure`,
`scalarAdditiveAtClosure`, and `scalarExactAtClosure`; their bodies are inlined in the
new `scalarAtClosure` definition. No DAG proof dependency was otherwise pruned.

## Where the brief, the DAG or earlier work was wrong

Earlier direct attempts correctly identified that the high and low ring-stage categories
share the same finite/integral presentations, but asking the kernel to unfold the
Ω/Ψ-dependent inclusion maps while checking `I.normalized` exceeded the 60-second file
limit. The remaining obligation is therefore recorded as the strictly smaller
normalization-equation transport theorem, while the certificate assembly itself is a
complete Lean proof.

## New nodes

`def-sf-ring-endpoint-scalar-at-closure` records the moved definition in
`Sheaf.Paper.RingEndpointScalarIdentityTransferData`.

`lem-sf-ring-endpoint-scalar-identity-normalization-transport` records the split
normalization equation in `Sheaf.Paper.RingEndpointScalarIdentityNormalization`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RingEndpointScalarIdentityNormalization": "b8878fb07111420b322ba177798650cd37070df3", "Sheaf.Paper.RingEndpointScalarIdentityTransfer": "a5518f87bc9c9f716a4ed625cd06e8e67ecd1ea0", "Sheaf.Paper.RingEndpointScalarIdentityTransferData": "3d76cfab81e246345851491328892e81fa766c7f"}, "results": {"Sheaf.Paper.RingEndpointScalarRestrictions": {"hash": "d86aa1bf59db722ba3c8eb5e30436cce548c0963", "status": "OK"}}, "seconds": 83, "time": "2026-10-28T07:47:41+0800", "transitive": 0, "version": 1}
```

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
