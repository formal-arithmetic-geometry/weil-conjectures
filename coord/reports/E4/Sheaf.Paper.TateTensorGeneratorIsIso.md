## What changed

Added the proof-only import `Sheaf.Paper.TateTensorGeneratorLocalIsIso` and proved
`tateTensorQuotient_generator_isIso` by applying the sheaf local isomorphism criterion
to the underlying additive sheaf and reflecting the resulting isomorphism through the
forgetful functor. Added the split-off local pointwise theorem and its DAG node.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.PurityIntegralTower.tateTensorQuotient_generator_isIso`
(1 of 1 item sorries). Added one lower-level sorry,
`AlgebraicGeometry.Scheme.PurityIntegralTower.tateTensorQuotient_generator_local_isIso`,
recorded by node `lem-pur-tate-tensor-generator-local-isiso`.

## No longer needed

The original geometric dependency list is no longer imported directly by the item proof;
the item uses the local theorem, the sheaf local-isomorphism criterion, and generic
forgetful-functor facts. No existing DAG module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the local rank-one calculation with the global sheaf descent.
Separating the pointwise calculation leaves a strictly simpler lower-level statement and
makes the global proof a short, complete categorical argument.

## New nodes

`lem-pur-tate-tensor-generator-local-isiso` records the pointwise local rank-one
isomorphism statement in `Sheaf.Paper.TateTensorGeneratorLocalIsIso`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.TateTensorGeneratorIsIso": "9b352826dabd2143f95237591fc1439c54d3a574", "Sheaf.Paper.TateTensorGeneratorLocalIsIso": "c7b5fcd66878a404e66f42b032548452afb28c02"}, "results": {"Sheaf.Paper.TateTensorQuotientBalancing": {"hash": "a1e4ae52fff774e5b68c9708d7606a69df8ce797", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T07:11:30+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
