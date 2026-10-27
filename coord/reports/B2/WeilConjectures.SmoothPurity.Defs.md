## What changed

Repaired the `smoothTrace` definition by taking the unique representing trace from the new
`existsUnique_smoothTrace` theorem on the smooth branch, with the explicit zero morphism on
the pre-existing nonsmooth extension of the unconditional source signature. Added the
proof-only import `Sheaf.SmoothPurity.TraceExistence` and its DAG node.

## Proved and sorry left

Closed the definition hole in `AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace`.
Added the strictly smaller theorem
`AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_smoothTrace`, whose geometric proof
remains `sorry` and is recorded by node `lem-route-smooth-trace-representing-unique`.
The existing holes left unchanged are `isIso_smoothPurityMap`,
`smoothPurityIso_zero_of_isOpenImmersion`, and `smoothPurityIso_comp_openImmersion`.
No definition contains `sorry`.

## No longer needed

None. The existing finite-purity, normalized tower, exceptional reconstruction, and Tate
realization imports remain needed by the new representing theorem or existing route.

## Where the brief, the DAG or earlier work was wrong

The prior source left `smoothTrace` as a `sorry` inside a definition, which stage 3 forbids.
The missing geometric construction is isolated as a strictly smaller representing-pair
statement; its uniqueness determines the chosen trace. The source's unconditional signature
is preserved by an explicit zero extension when no smoothness instance is available. The
unconditional `isIso_smoothPurityMap` statement is explicitly disputed upstream and remains
untouched.

## New nodes

Added `lem-route-smooth-trace-representing-unique` for the representing theorem used by the
repaired definition.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.SmoothPurity.TraceExistence": "8254b2cf476dd6d0b90a82ae7bf52e95b429a1c1", "WeilConjectures.SmoothPurity.Defs": "4d264fc9ff408698b207667d5dfc360b36c2e910"}, "results": {"Sheaf.Targets.SmoothPurityQbar": {"hash": "b61095f4237cc889a88d12105bb9497ef53983af", "status": "OK"}, "WeilConjectures": {"hash": "9e345e55f9726b5285733eab3860a92f26dd6979", "status": "OK"}, "WeilConjectures.PoincareDuality.Poincare": {"hash": "24c41d940617dccc117d662fe9a0ea621d946970", "status": "OK"}, "WeilConjectures.TraceFormula.Dualizing": {"hash": "6f0205d1db4c599fd319656d4acc1446b3c84ebb", "status": "OK"}}, "seconds": 115, "time": "2026-10-28T03:48:08+0800", "transitive": 0, "version": 1}
```

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
