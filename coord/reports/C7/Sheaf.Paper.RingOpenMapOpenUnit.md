## What changed

Proved `WeilConjectures.PurCompactSupport.openDerivedAdjunction_unit_isIso` in
`Sheaf.Paper.RingOpenMapOpenUnit`, preserving its statement. Added proof-only imports of
`Sheaf.AlgebraicGeometry.ProEtaleOpenSlicePresentation` and, using `import all`,
`Sheaf.Paper.OpenImmersionTensorPiece` for its already proved private localized derived-unit
helper. Derived the slice presentation, transported full faithfulness, and applied the
standard adjunction unit criterion. Updated the item node to record these dependencies.
The two integral site-size instances are disabled only for this theorem, as in the original
coefficient-data proof, to avoid a stuck universe constraint between site-size instances.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PurCompactSupport.openDerivedAdjunction_unit_isIso`
(node `lem-sf-ring-open-map-open-unit`). Added zero holes; zero sorries remain in the item.
No new statements or definitions. The proof reuses existing proved helpers and introduces
no split-off obligations. The argument applies to empty and identity open immersions as
well, with arbitrary coefficient sheaves and no quasi-compactness hypothesis.

## No longer needed

None. The original public coefficient-data import remains necessary for the statement.
Both added proof imports are used. No planned dependencies, nodes, or modules are pruned;
no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing argument already proves the needed full faithfulness inside
`openProjectionInverse_isIso`. The original item node mentioned only the coefficient-data
module; its proof dependency list now explicitly records the slice presentation and
open tensor module containing the proved localized derived-unit helper. No mathematical
statement repair was needed. Current server queue row is stage 3, proof/route with one
hole; no rework row or build-error record was present.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RingOpenMapOpenUnit": "8f29f7daf34a997a06558c1adf1d2ba7a388f062"}, "results": {"Sheaf.Paper.RingOpenMapInvertibility": {"hash": "e7a3a19d4808e6732d02a132863b10b32f781582", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T03:20:49+0800", "transitive": 0, "version": 1}
```

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
