## What changed

Filled `WeilConjectures.integralBraidingScalarExtensionSquare` by applying faithful coherent reduction to the finite-stage signed-swap square. Added the private proof import and the new module `Sheaf.Paper.ReducedIntegralBraidingScalarExtensionSquare`, whose named intermediate theorem records equality after coherent reduction.

## Proved and sorry left

The target theorem `WeilConjectures.integralBraidingScalarExtensionSquare` is proved. One strictly weaker intermediate theorem remains as `sorry`: `WeilConjectures.reducedIntegralBraidingScalarExtensionSquare`, recorded by node `lem-pur-integral-braiding-scalar-extension-square-reduced`.

## No longer needed

No imports, nodes, or modules were pruned. The target proof uses the reduced square and `lem-pod-integral-system-reduction-fully-faithful`; the other finite-stage dependencies are retained by the new intermediate node's stated proof route.

## Where the brief, the DAG or earlier work was wrong

The original four-step plan combines the finite-stage signed-swap calculation with the final fully faithful lifting. The Lean proof separates these two logically distinct steps: the finite-stage calculation is a strictly weaker reduction theorem, and the target is then obtained by faithfulness. No target statement or definition was changed.

## New nodes

`lem-pur-integral-braiding-scalar-extension-square-reduced` in `dag/nodes/sec-smooth-purity/lem-pur-integral-braiding-scalar-extension-square-reduced.json` records the equality after coherent reduction and is stated in `lean/Sheaf/Paper/ReducedIntegralBraidingScalarExtensionSquare.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralBraidingScalarExtensionSquare": "369859770a856cd86b884c202c075f6c43fa7c65", "Sheaf.Paper.ReducedIntegralBraidingScalarExtensionSquare": "564c77870668da585d95540b88f0764acc18e06d"}, "results": {}, "time": "2026-10-28T07:57:50+0800", "transitive": 0, "version": 1}
```

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
