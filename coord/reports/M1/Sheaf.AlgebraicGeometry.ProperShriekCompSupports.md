## What changed

The assigned module now proves `properRouteCompIso_refl` and
`properShriekComp_comp_forgetSupports`. The parent proof substitutes the specified
composite equality and applies the new canonical-composite intermediate theorem.
The direct raw-compositor import was removed from the parent module; the new
canonical-composite module imports it privately as the proof dependency of its
split-off theorem.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.properShriekComp_comp_forgetSupports` and retained
the previously closed `AlgebraicGeometry.Etale.properRouteCompIso_refl`.
Added one strictly smaller split-off obligation,
`AlgebraicGeometry.Etale.properShriekComp_comp_forgetSupports_canonical`, in
`lem-sf-proper-shriek-compositor-supports-canonical`.

## No longer needed

The assigned module no longer directly imports
`Sheaf.AlgebraicGeometry.ProperShriekCompSupportsRaw`; that dependency is owned by
the canonical-composite split module. No DAG dependency is mathematically pruned;
the raw calculation remains needed below the new split-off theorem.

## Where the brief, the DAG or earlier work was wrong

The direct application of the raw theorem does not elaborate within the file time
limit because the parent carries an explicit `[IsProper (p ≫ f)]` instance while
the raw theorem's canonical-composite instance is synthesized. Isolating the
canonical-composite statement with that instance explicit gives a strict
specialization and lets the parent proof compile quickly. The natural-language
route is otherwise unchanged.

## New nodes

`lem-sf-proper-shriek-compositor-supports-canonical` records the canonical-composite
specialization used by the parent. Its proof plan first normalizes the route
compositor and then applies the existing raw compositor calculation.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProperShriekCompSupports": "ba5dcb3b4318d759f91d7e1518e22ab4f94b2e36", "Sheaf.AlgebraicGeometry.ProperShriekCompSupportsCanonical": "b08245b0d8313f3d53b3d7507f5e5a133fc758d2"}, "results": {"Sheaf.AlgebraicGeometry.ProperRelativeKunnethSupports": {"hash": "9230550da94be91d4661a5aaf741024aa58cd4ae", "status": "OK"}}, "seconds": 58, "time": "2026-10-28T05:38:21+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
