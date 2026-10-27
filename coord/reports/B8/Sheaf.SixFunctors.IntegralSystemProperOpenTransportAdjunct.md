## What changed

Added the explicit `transportedGamma` construction, obtained by conjugating the intrinsic
`SemilinearProperOpen.gamma` through the canonical bridge isomorphisms. The target theorem
now assembles this construction with the adjunct-normalization field. The remaining
adjunct identity is recorded as the strictly simpler `transportedGamma_adjunct` theorem.

## Proved and sorry left

The `transportedGamma` definition is fully proved, and
`integralSystemProperOpenTransportAdjunct` is reduced to its explicit transported gamma
and one field theorem. One sorry remains in `transportedGamma_adjunct`, which states the
adjunct equation for that fixed explicit gamma and has a new DAG node.

## No longer needed

None. The existing public import is sufficient for the bridge and intrinsic proper/open
maps used by the construction.

## Where the brief, the DAG or earlier work was wrong

The DAG's single adjunct node bundled the bridge conjugation construction and its mate
calculation. Separating the explicit natural transformation from its adjunct equation
makes the remaining obligation a genuine field-level statement while preserving the
original target statement.

## New nodes

`lem-sf-integral-system-proper-open-transport-adjunct-normalization` records the adjunct
identity for the explicit `transportedGamma` construction.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunct": "091c04fbeb8f9168e8540758403e567073528777"}, "results": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportCanonical": {"hash": "f248118d8fe44ea92aed6b69e0329d390636cde7", "status": "OK"}}, "seconds": 13, "time": "2026-10-28T06:29:59+0800", "transitive": 0, "version": 1}
```

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
