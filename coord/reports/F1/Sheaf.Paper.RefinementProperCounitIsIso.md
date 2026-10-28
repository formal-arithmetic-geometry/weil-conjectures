## What changed

Removed proof-only imports that are not used by the remaining declarations. The two existing theorem holes remain unchanged because proof terms that force conversion of the derived-category morphism exceed the compiler limit.

## Proved and sorry left

Proved: none.

Sorry left:

- `WeilConjectures.PurCompactSupport.refinementProperCounit_isIso`
- `WeilConjectures.PurCompactSupport.refinementRestriction_factorization`

No new sorry declarations were added.

## No longer needed

The proof-only imports removed from this module are:

- `Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenPullbackKInjective`
- `Sheaf.AlgebraicGeometry.ProEtaleIdentifiedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.Paper.IntegralFinitePullbackComposition`

No DAG dependencies were removed; they remain needed by the pending proper-counit proof route.

## Where the brief, the DAG or earlier work was wrong

The factorization node describes the proof as reflexivity after unfolding. The unfolded equality is exact, but checking reflexivity of the resulting large morphism term exceeds the compiler fixed limit; the generated `refinementRestriction.eq_def` theorem has the same conversion cost at this use site.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RefinementProperCounitIsIso": "7262356201ebe92c3fc6194cf1726a392fcb5fe8"}, "results": {"Sheaf.Paper.RefinementOpenRestrictionComponentIsIso": {"hash": "232e5656c54ff849086d1cb59d942ebfdf8cc972", "status": "OK"}}, "seconds": 10, "time": "2026-10-28T08:59:32+0800", "transitive": 0, "version": 1}
```

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
