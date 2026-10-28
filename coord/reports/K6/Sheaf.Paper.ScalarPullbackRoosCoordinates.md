## What changed

The returned split-off statements were withdrawn because their interfaces did not
identify the canonical coordinate isomorphism or its generator normalization. The
item theorem is restored to its single named proof obligation, with its tensor-unit
predicate retained in the dedicated `ScalarPullbackQuotientFormula` module. The
computability theorem is unchanged.

## Proved and sorry left

`scalarPullbackRoosCoordinates_exists` remains one sorry. No additional theorem is
claimed as proved or split off. The definition `ScalarPullbackQuotientFormula` has no
sorry.

## No longer needed

The split-off modules `ScalarPullbackRoosCoordinatesIso` and
`ScalarPullbackRoosCoordinatesGenerator` are withdrawn. No original proof dependency
is removed; the ordinary quotient comparison declarations remain the dependencies
recorded for the item.

## Where the brief, the DAG or earlier work was wrong

The earlier split quantified the generator equation over an arbitrary isomorphism,
which is false because composing an isomorphism with a sign automorphism can negate
the generator. Its companion existence theorem concluded only `True`, so it did not
identify a coordinate isomorphism that could be used by the generator theorem. The
item is therefore left as one hole pending the construction of the canonical
comparison isomorphism and its formula.

## New nodes

- `stage3-pur-scalar-pullback-roos-coordinates-formula`

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.ScalarPullbackQuotientFormula": "116858f071259e52ad930a3647ab13b9ae320950", "Sheaf.Paper.ScalarPullbackRoosCoordinates": "f414367df227bfee1e11e4c84df6dad4fb3f8490"}, "results": {"Sheaf.Paper.ScalarPullbackLeftRoos": {"hash": "6ae27fc14fdcd315db34e2b40fd18df92ec06d96", "status": "OK"}, "Sheaf.Paper.ScalarPullbackRightRoos": {"hash": "7b9eb3cb1a48f5d3e95b8b08dc33dabfcc53d05d", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T08:29:26+0800", "transitive": 0, "version": 1}
```

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
