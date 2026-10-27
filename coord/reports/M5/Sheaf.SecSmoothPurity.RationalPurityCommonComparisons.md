## What changed
Added the named theorem `WeilConjectures.RationalPurityCoherence.commonSupportComposition_exists`
with the original finite-stage existence obligation as a split-off theorem. Proved the
original `commonSupportComposition_existsUnique` theorem from that existence statement by
`Iso.ext`, `NatTrans.ext`, and the prescribed component equations. No imports were added or
removed.

## Proved and sorry left
The `commonSupportComposition_existsUnique` hole is closed. One strictly simpler hole remains:
`commonSupportComposition_exists`, recorded by
`lem-pur-rational-common-support-composition-existence`.

## No longer needed
None. The proof uses only the new split theorem; all module imports remain required by the
other declarations in this compilation subdivision.

## Where the brief, the DAG or earlier work was wrong
The existing theorem combined finite-stage descent and uniqueness in one `sorry`. The
componentwise uniqueness is elementary once existence is named, so it is now proved directly;
the descent obligation remains as the split node.

## New nodes
`lem-pur-rational-common-support-composition-existence` records the finite-stage existence
obligation and uses the existing rational purity and coefficient comparison dependencies.
The interface addition is recorded in
`coord/changes/common-support-composition-existence.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SecSmoothPurity.RationalPurityCommonComparisons": "2b8a76033ed0141a0c750ad88d4f804323a159e7"}, "results": {"Sheaf.SecSmoothPurity.RationalPurityTraceCoherence": {"hash": "0091913289529cd60ce8938cc38e96ee7a2ce7a4", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T04:21:42+0800", "transitive": 0, "version": 1}
```

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
