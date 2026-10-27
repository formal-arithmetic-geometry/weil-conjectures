## What changed

The target module now imports two lower structural modules and proves
`AlgebraicGeometry.Scheme.ProEt.clopen_structural_data` by combining their
strictly smaller conclusions. The lower modules isolate the normalized tensor
comparison clause and the coproduct/zero-insertion clause.

## Proved and sorry left

Closed the original `clopen_structural_data` sorry (1 of 1). Added two named
lower statements, each with one documented `sorry`: `clopen_structural_comparison`
(node `lem-pur-clopen-structural-comparison`) and
`clopen_structural_coproduct_adjunction` (node
`lem-pur-clopen-structural-coproduct-adjunction`). Thus 2 split-off holes remain.

## No longer needed

None. The parent target's declared tensor, gluing, and signed-coherence
dependencies remain available to the lower statements and no imported module was
removed.

## Where the brief, the DAG or earlier work was wrong

The DAG presented the full tensor comparison, differential, symmetry, arbitrary
coproduct, and arbitrary zero-insertion adjunction construction as one proof
step. No existing declaration supplies that whole construction directly, so the
step was reduced into the two named clauses above while preserving the target
statement and the unit route.

## New nodes

`lem-pur-clopen-structural-comparison` records the first conjunct, including all
pure-tensor, total-summand, differential, and signed-symmetry equations.

`lem-pur-clopen-structural-coproduct-adjunction` records the remaining coproduct
preservation and zero-insertion adjunction conjuncts.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralComparison": "d42ae247188e2f9553d792eefb33fa7c9d88e564", "Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralCoproductAdjunction": "fbd54972a3d7e0b8eeb1f6d22d6bd08fa9571c0d", "Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralData": "fe1ca2c8a4ea5d15d5a0b6340fefd26ed2d2b48c"}, "results": {}, "time": "2026-10-28T02:20:32+0800", "transitive": 0, "version": 1}
```

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
