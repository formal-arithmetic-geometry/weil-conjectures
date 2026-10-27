## What changed

The item module now constructs flat-term K-flat resolutions for arbitrary derived inputs using
`CochainComplex.exists_quasiIso_flat_kFlat` and reduces the target equation to transport along
two representative isomorphisms.  The remaining transport calculation is isolated in the new
module `Sheaf.Paper.QuotientSectionTensorTransportIso`.

## Proved and sorry left

The resolution construction and reduction in
`tensor_section_condition_of_kflat` are proved.  The new theorem
`tensor_section_condition_transport_iso` remains a named `sorry` for the naturality and
cancellation calculation; node `lem-sfb-quotient-section-tensor-transport-iso` records it.

## No longer needed

No proof-dependency imports or existing nodes were pruned.  The previous direct proof attempt
needed only the representative-resolution API and the new transport node.

## Where the brief, the DAG or earlier work was wrong

The DAG proof step omitted the separate transport calculation needed after choosing resolutions.
That calculation is strictly smaller than the universal extension statement and is now recorded as
a new node.

## New nodes

`lem-sfb-quotient-section-tensor-transport-iso` in
`dag/nodes/sec-six-functors-basics/lem-sfb-quotient-section-tensor-transport-iso.json`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.QuotientSectionTensorTransportExtension": "00fd37e2979c094d5361b77e160c27258aa785cc", "Sheaf.Paper.QuotientSectionTensorTransportIso": "4a188f09f4dab254043b5e601f777e3dc1e91ead"}, "results": {}, "time": "2026-10-28T03:55:35+0800", "transitive": 0, "version": 1}
```

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
