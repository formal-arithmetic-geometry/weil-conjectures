## What changed

Proved `finiteDualizing_affineRestriction_isIso` by importing the split global mate
invertibility statement and transporting it through the affine derived inverse-image
functor. Added `Sheaf.SixFunctors.AffineRestrictionMapIso` for that split statement. The change record is `coord/changes/affine-restriction-map-iso.md`.

## Proved and sorry left

Closed `finiteDualizing_affineRestriction_isIso` (one of one original holes). Added one
split hole, `finiteDualizing_etaleComparison_factorization`, whose statement is the global mate
invertibility step used before affine restriction.

## No longer needed

None. The assigned module still needs `FiniteDualizingData`; the helper imports only the
finite dualizing data and categorical isomorphism infrastructure.

## Where the brief, the DAG or earlier work was wrong

The global build record contained a stale bad-import report for
`Sheaf.SixFunctors.FiniteDualizingData`; the module is present and compiled successfully
in this sandbox. The proof route was reduced to the global mate factorization step plus
functorial transport; the latter is now explicit in the helper module.

## New nodes

Added `affine-restriction-map-iso` for `finiteDualizing_etaleComparison_factorization`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.AffineRestrictionMapIso": "c0f591f50771d34f28a971ee9e8e02e4a42ae24e", "Sheaf.SixFunctors.FiniteDualizingAffineRestriction": "8377f8ccce26f4213dbce74be8f46cc1866d3146"}, "results": {"Sheaf.SixFunctors.FiniteDualizing": {"hash": "cf1d04c0140d20e7b2f193288b7c1ecb21a5346c", "status": "OK"}}, "seconds": 51, "time": "2026-10-28T06:50:57+0800", "transitive": 0, "version": 1}
```

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
