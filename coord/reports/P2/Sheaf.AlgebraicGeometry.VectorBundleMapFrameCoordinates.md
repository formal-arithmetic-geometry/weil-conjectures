## What changed

Proved `AlgebraicGeometry.VectorBundleZeroSection.map_frame_coordinates` in
`Sheaf.AlgebraicGeometry.VectorBundleMapFrameCoordinates`, preserving its signature and the
bodies and signatures of `pulledFrame` and `framedPullbackMap`.

The proof uses private, proved helpers for adjunction mates, evaluating pulled frames,
the degree-one linear map induced by a lift to a bundle, finite free-module pairings, and
preservation of the ordered affine-tower coordinates. Its only added import is a private
proof import of `WeilConjectures.CategoryTheory.CommAlgebraSheafModule`. The node's proof
and proof dependencies describe this argument. No other existing module is changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.VectorBundleZeroSection.map_frame_coordinates`
(node `lem-pur-vector-bundle-map-frame-coordinates`).

No holes added, no split-off statements, and no `sorry` left in the delivered module.
The remote single-file compile passed cleanly in 31.5 seconds.
The argument does not assume invertibility of the module map, equal ranks, affineness
or nonemptiness of W. Finite coproduct identities handle empty target bases, and a source
coordinate in rank zero has no index.

## No longer needed

No module or import is pruned. The separate tensor-pullback adjunction bridge
`lem-pc-module-pullback-adjunction` is not used in this proof: the statement's canonical
`Scheme.Modules.pullbackPushforwardAdjunction` and Mathlib's mate-compatible composition
and restriction comparisons suffice. Its module remains imported transitively by
`VectorTraceGeometry` for other declarations, so this is not claimed as closure pruning.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The generator calculation can be completed through
module morphisms and adjunctions without new affine-local symmetric-algebra lemmas.
The current blueprint proof discusses base-change compatibility at the level of local
integration; the explicit degree-one algebra calculation used here is justified by the
recorded Stacks source, `constructions.tex`, `lemma-spec-properties` and
`lemma-category-vector-bundles`. No unit statement or unit proof step is bypassed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.VectorBundleMapFrameCoordinates": "423f3e2fe21d1391a878df5b5887b575f48327a9"}, "results": {"Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeCoordinates": {"hash": "5ef8eb01b56724cdb37b70e3ee2e3903f9e66594", "status": "OK"}}, "seconds": 267, "time": "2026-10-28T14:24:23+0800", "transitive": 0, "version": 1}
```

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
