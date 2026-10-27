## What changed

Proved `finitePartialTensor_identityNaturality_coordinates` by expanding the
left comparison with `pullbackTensor_fixed_coordinates` and applying the named
remaining fixed-coordinate naturality calculation. Added the intermediate
module `Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinatesExpanded`.

## Proved and sorry left

Closed the `sorry` in
`WeilConjectures.finitePartialTensor_identityNaturality_coordinates`.
The added intermediate declaration
`WeilConjectures.finitePartialTensor_identityNaturality_coordinates_expanded`
remains `sorry` (node
`lem-sf-finite-partial-tensor-identity-naturality-coordinates-expanded`); it is
the strictly smaller scalar naturality calculation after the comparison has
been expanded.

## No longer needed

No imports or declared dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The existing DAG proof plan identifies the fixed-coordinate expansion but does
not provide a declaration for the remaining two-input scalar naturality
calculation. That calculation was split into the new node listed below.

## New nodes

`lem-sf-finite-partial-tensor-identity-naturality-coordinates-expanded` is stated
in `lean/Sheaf/Paper/FinitePartialTensorIdentityNaturalityCoordinatesExpanded.lean`.
Its node file is
`dag/nodes/sec-six-functors/lem-sf-finite-partial-tensor-identity-naturality-coordinates-expanded.json`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinates": "87deb84557584fc8ae34bd70647e70c337c1b1ff", "Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinatesExpanded": "84220d6052047045652ad705eb6efa74fa47a413"}, "results": {}, "time": "2026-10-28T06:54:47+0800", "transitive": 0, "version": 1}
```

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
