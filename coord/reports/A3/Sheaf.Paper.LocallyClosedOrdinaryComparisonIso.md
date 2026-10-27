## What changed

Filled `AlgebraicGeometry.Etale.locallyClosedOrdinaryComparison_isIso` without
changing its statement. The proof constructs the required Noetherian, compact,
finite type and coefficient exponent instances, applies
`finiteCoefficientDirectImageMap_isIso` to `j ≫ g`, and uses
`finiteCoefficientDirectImageMap_comp` to extract the ordinary comparison as an
isomorphism. The redundant direct import of `Sheaf.Paper.EtaleLocallyClosedShriek`
was removed because it is already public through `InternalAdjunctionPairingChange`.

## Proved and sorry left

Closed the one original hole, `locallyClosedOrdinaryComparison_isIso`. There are
no `sorry`s left in the delivered module and no split-off obligations.

## No longer needed

The direct `EtaleLocallyClosedShriek` import was unused by the proof and was
removed. Every declaration in the node's stated proof route is still used;
no dependency node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The quarantined source had stale imports that failed against the current
published dependency set. The planned cancellation can be expressed directly
with `IsIso.of_isIso_comp_left` and `IsIso.of_isIso_comp_right`, avoiding a
separate cancellation lemma or intermediate statement.

## New nodes

None.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LocallyClosedOrdinaryComparisonIso": "f0e29ee6b852e5b564a2abed58105232b75a3724"}, "results": {"Sheaf.Paper.LocallyClosedHomGenerator": {"hash": "0ddf5833c3be54d15e7bbdfa4e9d00913bb586b9", "status": "OK"}}, "seconds": 67, "time": "2026-10-28T02:06:06+0800", "transitive": 0, "version": 1}
```

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
