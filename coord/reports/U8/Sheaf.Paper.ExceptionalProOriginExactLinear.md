## What changed

Restored the quarantined module and proved the additive, shift, and triangulated
structures for the pro-etale compact-support composite and the transported right
composite. The proof uses the recorded derived comparison factors, exactness of the
ordinary inverse images, and the adjunction shift and triangulation APIs. The scalar
construction was split into the smaller theorem
`AlgebraicGeometry.exceptionalProScalarActions` in
`Sheaf.Paper.ExceptionalProScalarActions`, which the main theorem now combines with
the proved exactness data.

## Proved and sorry left

Closed the original `exceptionalProOriginExactLinear` hole. One strictly smaller
hole remains in `exceptionalProScalarActions`, covering only the two scalar-action
packages and their linearity equations.

## No longer needed

The original proof plan's separate dependencies
`lem-sf-exact-functor-derived-triangulated` and
`lem-pc-right-derived-functor-triangulated` are not needed as declarations: the
proof obtains the same structure directly from the derived comparison factors and
adjunction APIs. No imported module was removed.

## Where the brief, the DAG or earlier work was wrong

The quarantined source was reported by the global build only as a missing file path;
the actual module still contained its original sorry. The previous plan treated the
generic exact-derived structure as separate project lemmas, but the existing APIs
already construct the required structures directly. The scalar portion is now an
explicit smaller DAG node.

## New nodes

`lem-sf-exceptional-pro-origin-scalar-actions` —
`Sheaf.Paper.ExceptionalProScalarActions`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalProOriginExactLinear": "278e72932fdf88276bc498145e0fd01605a002c7", "Sheaf.Paper.ExceptionalProScalarActions": "45146d313c794ecc781f94cdd053d9867f330cb5"}, "results": {"Sheaf.Paper.ExceptionalSystemTransport": {"hash": "5c64defc13e63e8cf084e585bdb77528a7b5bbc7", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralSystemExistence": {"hash": "3a2762881292a445abf50cc8f61fb3b3c0be90cb", "status": "OK"}}, "seconds": 137, "time": "2026-10-28T01:11:39+0800", "transitive": 0, "version": 1}
```

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
