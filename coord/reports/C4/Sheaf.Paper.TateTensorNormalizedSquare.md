## What changed

The item theorem now extracts the two fixed projection-normalized models at indices `b` and `a` and applies a new fixed-pair theorem. The new module `Sheaf.Paper.TateTensorNormalizedSquarePair` isolates the scalar and tensor calculation for selected models; its theorem is the remaining stage-3 hole. The item imports this proof-only module.

## Proved and sorry left

The item declaration `AlgebraicGeometry.Scheme.PurityIntegralTower.tateTensor_normalizedSquare` is proved from the fixed-pair theorem. One new sorry remains in `AlgebraicGeometry.Scheme.PurityIntegralTower.tateTensor_normalizedSquare_of_pair`, node `lem-pur-tate-tensor-normalized-square-pair`. Holes closed: 1. Holes added: 1. The added statement is strictly a fixed-pair component: it assumes selected ordinary models and their balancing/evaluation clauses instead of the all-index `ProjectionNormalized` predicate.

## No longer needed

No existing dependency is pruned. The proof uses the new fixed-pair module and the data module already imported by the item.

## Where the brief, the DAG or earlier work was wrong

The prior delivery left the whole square as a single sorry. The all-index predicate contains the two local models needed for one pair, so the obligation can be reduced to a fixed-pair scalar/tensor calculation. No target statement or definition changed.

## New nodes

`lem-pur-tate-tensor-normalized-square-pair` records the fixed-pair scalar square and its source proof. The corresponding Lean declaration is in `lean/Sheaf/Paper/TateTensorNormalizedSquarePair.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.TateTensorNormalizedSquare": "5c88e655ad302df2002923a5cefacf27856e2cb1", "Sheaf.Paper.TateTensorNormalizedSquarePair": "a2fa6698d2db48c6004002f632c8926a418980b4"}, "results": {}, "time": "2026-10-28T03:42:29+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
