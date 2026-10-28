## What changed

Filled the normalization theorem in
`Sheaf.SixFunctors.IntegralSystemProperOpenTransportCanonicalMate`. The proof uses
adjunction injectivity, the chosen adjunct field, and the transported-gamma adjunct
normalization. The remaining bridge mate computation is isolated as the named
`properOpenTransportMate_adjunct` theorem in the same module.

## Proved and sorry left

Proved `properOpenTransportMate_normalized`.

One sorry remains: `properOpenTransportMate_adjunct`, represented by node
`lem-sf-integral-system-proper-open-transport-core-canonical-mate-adjunct`.

## No longer needed

No imports were removed. No declared proof dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's normalized-mate step requires a separate bridge-transpose calculation
before the final uniqueness argument can be checked within the compiler limit. The
split theorem is strictly the adjunct characterization of the transported mate,
while the delivered theorem combines it with the supplied adjunct field.

## New nodes

`lem-sf-integral-system-proper-open-transport-core-canonical-mate-adjunct` records the
remaining canonical bridge transpose calculation.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportCanonicalMate": "b471423e58f0dfeffe9bcb6252a55e09aced5344"}, "results": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportIntrinsicMate": {"hash": "008611a6315e20c058c05d12d8b518acf1df38ea", "status": "OK"}}, "seconds": 20, "time": "2026-10-28T10:03:09+0800", "transitive": 0, "version": 1}
```

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
