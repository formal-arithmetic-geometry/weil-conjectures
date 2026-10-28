## What changed

Proved `AlgebraicGeometry.Etale.properShriekComp_comp_forgetSupports_canonical` in
`lean/Sheaf/AlgebraicGeometry/ProperShriekCompSupportsCanonical.lean`. The proof factors the
canonical route through a component normalization lemma and an explicit-instance form of the
raw compositor calculation. Added `ProperShriekCompSupportsCanonicalHelper.lean` containing the
normalization lemmas and the split-off explicit-instance raw statement.

The item's direct import of `Sheaf.AlgebraicGeometry.ProperShriekCompSupportsRaw` was removed;
the helper module provides the dependency boundary.

## Proved and sorry left

Closed the item's `properShriekComp_comp_forgetSupports_canonical` sorry.

Added one strictly lower statement, with its proof left as `sorry`:
`AlgebraicGeometry.Etale.properShriekComp_comp_forgetSupports_raw_with_comp` in
`lem-sf-proper-shriek-compositor-supports-raw-explicit`.
It is the raw compositor calculation with the composite `IsProper` instance explicit, needed to
align the instance in the canonical target.

## No longer needed

The item's direct import of `Sheaf.AlgebraicGeometry.ProperShriekCompSupportsRaw` is no longer
needed after routing through the helper module. No proof-plan node is otherwise pruned.

## Where the brief, the DAG or earlier work was wrong

The canonical target carries an explicit `[IsProper (p ≫ f)]` instance, while the existing raw
statement infers composite properness from `[IsProper p]` and `[IsProper f]`. Direct rewriting or
proof-irrelevance transport between those elaborated terms exceeded the single-file kernel time
limit. The new lower statement records that instance-alignment step explicitly, preserving the
stated canonical proof route.

## New nodes

`lem-sf-proper-shriek-compositor-supports-raw-explicit` records the explicit-instance raw
compositor statement and its source step. Its Lean declaration is in
`lean/Sheaf/AlgebraicGeometry/ProperShriekCompSupportsCanonicalHelper.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProperShriekCompSupportsCanonical": "72833df6ee278ad12cbce0a27bf9d37be0964aa5", "Sheaf.AlgebraicGeometry.ProperShriekCompSupportsCanonicalHelper": "8a986d6d3f6102502192e700fcdcf91e4ead2e80"}, "results": {"Sheaf.AlgebraicGeometry.ProperShriekCompSupports": {"hash": "ba5dcb3b4318d759f91d7e1518e22ab4f94b2e36", "status": "OK"}}, "seconds": 16, "time": "2026-10-28T08:42:59+0800", "transitive": 0, "version": 1}
```

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
