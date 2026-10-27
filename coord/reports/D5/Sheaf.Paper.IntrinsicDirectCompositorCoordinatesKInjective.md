## What changed

Added the proof-only mate-pasting module and proved the assigned declaration by a real transitivity
calculation through `sfIntrinsicAmbientIntermediate`. The intermediate module records the fixed-scalar
transport construction and two strict normalization statements.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.sfIntrinsicDirectCompositorCoordinates_kInjective`.
The split module leaves these two named normalization theorems as `sorry`:

- `AlgebraicGeometry.Scheme.sfIntrinsicDirectCompositorCoordinates_ambient_normalization`
- `AlgebraicGeometry.Scheme.sfIntrinsicDirectCompositorCoordinates_ambient_to_intrinsic`

The supporting definitions `sfTransportRight` and `sfIntrinsicAmbientIntermediate` contain no `sorry`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original proof plan combines the ambient mate calculation with two independent transport
normalizations. The delivery separates those normalization steps into strict intermediate statements;
the assigned theorem combines them with transitivity.

## New nodes

`lem-sf-intrinsic-direct-compositor-coordinates-k-injective-mate-pasting` now records the fixed-scalar
intermediate and both normalization theorems in
`lean/Sheaf/Paper/IntrinsicDirectCompositorCoordinatesMatePasting.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntrinsicDirectCompositorCoordinatesKInjective": "e5871106a2f9e0aacfb79ca831711d4c455b18b8", "Sheaf.Paper.IntrinsicDirectCompositorCoordinatesMatePasting": "58a712c24860fcd95dea5a62625d6b9c4e8b395b"}, "results": {}, "time": "2026-10-28T04:49:26+0800", "transitive": 0, "version": 1}
```

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
