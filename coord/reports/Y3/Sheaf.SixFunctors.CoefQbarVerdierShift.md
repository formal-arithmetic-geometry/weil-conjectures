## What changed

Added `Sheaf.SixFunctors.CoefQbarVerdierShiftCore`, a split-off theorem for the
common-stage shift descent with a prescribed exact shift at each finite stage.
The original theorem now chooses the finite exact shifts from
`RationalVerdier.Datum.exact`, invokes the core, and packages the resulting
comparison squares. The item node records this proof dependency.

## Proved and sorry left

`WeilConjectures.CoefQbarVerdier.descended_shift_compatibility` is proved by
combining the finite datum exactness field with the split-off descent theorem.
The new declaration
`WeilConjectures.CoefQbarVerdier.descended_shift_core` remains one intentional
`sorry`, because its representative-level naturality and zero/addition descent
are the strictly smaller common-stage coherence step assigned to a follow-up
worker (node `lem-coef-qbar-verdier-shift-core-Y3`). No definition contains a
`sorry`.

## No longer needed

None. The existing public imports remain necessary for the statement and proof;
the proof-only import of `CoefQbarVerdierShiftCore` is required by the new route.

## Where the brief, the DAG or earlier work was wrong

The original module's proof plan bundled the representative-level common-stage
descent with the finite exactness packaging. The finite exactness is already
provided by `RationalVerdier.Datum.exact`; the genuinely separate missing step
is the descent core, which is now an explicit node rather than an unstructured
hole.

## New nodes

`lem-coef-qbar-verdier-shift-core-Y3` in
`dag/nodes/sec-six-functors/lem-coef-qbar-verdier-shift-core-Y3.json` records the
strictly smaller common-stage descent theorem and its source proof obligations.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarVerdierShift": "e887573e7e44a71998c6d9c220febdc9f800946f", "Sheaf.SixFunctors.CoefQbarVerdierShiftCore": "c987c124320ac7f7cad2ea68f394c90e6bdb63a5"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdierExactness": {"hash": "5fa89bdeee8a2e4cebed792565f07cc168c0040c", "status": "OK"}}, "seconds": 41, "time": "2026-10-28T09:53:10+0800", "transitive": 0, "version": 1}
```

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
