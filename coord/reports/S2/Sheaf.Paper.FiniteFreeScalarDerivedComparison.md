## What changed

`Sheaf.Paper.FiniteFreeScalarDerivedComparison` now proves
`finiteFreeScalarProjection` from the Mathlib triangle two-out-of-three lemma.
The finite-free cone construction is recorded as the split-off theorem
`finiteFreeScalarProjection_triangle` in the new module
`Sheaf.Paper.FiniteFreeScalarProjectionTriangle`.
The item's proof dependencies now use that triangle package and
`CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂`.

## Proved and sorry left

The item's `finiteFreeScalarProjection` sorry was closed.  The delivery adds one
strictly smaller named statement, `finiteFreeScalarProjection_triangle`, whose
proof remains `sorry`; it records the distinguished triangles, the isomorphisms
on the first two components, and the exact transported third component needed by
the target.  No definition contains `sorry`.

## No longer needed

No imports were removed.  The ringed projection-mate exactness and native tensor
interfaces remain needed by the split-off triangle theorem, while the item itself
uses only the split theorem and the Mathlib triangle lemma for its final step.

## Where the brief, the DAG or earlier work was wrong

The original node's planned cone construction is not directly available as a
single declaration in the current Lean interfaces.  It has therefore been split
at the genuine proof boundary: constructing the exact triangle morphism is a
strictly smaller theorem, and the item proves the projection isomorphism from it
by a complete two-out-of-three argument.  The target statement and all existing
definitions are unchanged.

## New nodes

`lem-sfb-finite-free-scalar-projection-triangle` records the finite-free
triangle-morphism construction and is stated in
`Sheaf.Paper.FiniteFreeScalarProjectionTriangle`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteFreeScalarDerivedComparison": "4f41319fd3f7a83e8625167050113e4307a8b6f6", "Sheaf.Paper.FiniteFreeScalarProjectionTriangle": "bce7d0cd42525c9314f087bdd2da738e42ea7221"}, "results": {}, "time": "2026-10-28T07:58:35+0800", "transitive": 0, "version": 1}
```

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
