## What changed

The item theorem `scalarPullbackRightRoos` is now proved by a real composition
calculation from the new normalization theorem
`scalarPullbackRightRoos_normalized`. The item imports that proof module and
reassociates the explicit ordinary tail with `scalarPullbackRoosChain`. The
normalization theorem is isolated in
`Sheaf.Paper.ScalarPullbackRightRoosNormalization`; its statement omits the
quotient-generator hypothesis `hq`, because that hypothesis belongs only to the
subsequent quotient identification.

## Proved and sorry left

The original `scalarPullbackRightRoos` sorry is closed (1 of 1 item sorries).
One strictly simpler intermediate theorem remains as a named split-off sorry:
`scalarPullbackRightRoos_normalized`, recorded by node
`stage3-pur-scalar-pullback-right-roos-normalized`. No definition contains a
sorry.

## No longer needed

No imports were removed. The item proof directly uses the new normalization
module and `ScalarPullbackRoosCoordinates`; all other proof dependencies remain
in the split theorem's DAG proof plan. The `hq` hypothesis remains in the item
interface unchanged, although the normalization subtheorem does not use it.

## Where the brief, the DAG or earlier work was wrong

The original node bundled scalar/pullback normalization and the explicit
quotient-generator identification into one theorem. The delivery separates
the normalization equation as a strictly simpler intermediate statement; the
item theorem then combines it with the definitional ordinary tail. No target
statement or existing declaration was changed.

## New nodes

`stage3-pur-scalar-pullback-right-roos-normalized` records the normalization
subtheorem in `lean/Sheaf/Paper/ScalarPullbackRightRoosNormalization.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ScalarPullbackRightRoos": "610f65e364601c161baf6a78426ea5699d2491a5", "Sheaf.Paper.ScalarPullbackRightRoosNormalization": "fec53bdfd6a71886ed35109c3432801feec3b77c"}, "results": {}, "time": "2026-10-28T08:00:01+0800", "transitive": 0, "version": 1}
```

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
