## What changed

Proved `ordinaryProjectionSquare` with its original signature. Invert the
existing `canonicalReductionTensorPull` equation to supply the compatibility
hypothesis of the adopted source-library theorem
`Adjunction.rightAdjointProjectionMap_mate`. The counit mate identity supplies
the direct-image comparison. Tensor and projection naturality then insert both
expression coefficient maps. All auxiliary constructions and lemmas are private
and proved inside the assigned module.

Validation: the complete module compiled without warnings in 18.5 seconds. The
proof uses arbitrary expression coefficient maps; identity maps and zero objects
require no separate assumptions.

## Proved and sorry left

Closed 1 of 1 original holes: `ordinaryProjectionSquare`.
There are zero remaining holes in the item, and zero holes added or split off.
The existing imported `canonicalReductionTensorPull` statement is used as a
proof dependency; its proof remains the work of its own item.

## No longer needed

This proof does not require the planned dependency nodes
`lem-sf-integral-ordinary-canonical-iso-square`,
`lem-sf-tensor-adjunction-reduction-squares`, or
`lem-weil-pbc-ringed-exchange-tensor-coherence`. The more specific existing
`lem-sf-canonical-reduction-tensor-pull` plus the adopted generic projection mate
theorem suffices. Those other nodes can still have independent consumers.
No original public import was removed; only two private proof imports were added.
No source-library declaration or module was removed.

## Where the brief, the DAG or earlier work was wrong

The former DAG plan cited larger coherence results, although the normalized
primitive tensor/pullback square already supplies exactly the generic mate
compatibility hypothesis. The Lean proof follows the same unit/counit mate
argument with this shorter dependency route. No statement or definition changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralOrdinaryProjectionSquare": "ed5b41afdbd68fd41b1585f4776e7c57c1b3ef76"}, "results": {"Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares": {"hash": "70262e517d2b5ef75dbd07b19bcac239bff5a686", "status": "OK"}}, "seconds": 28, "time": "2026-10-28T04:49:43+0800", "transitive": 0, "version": 1}
```

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
