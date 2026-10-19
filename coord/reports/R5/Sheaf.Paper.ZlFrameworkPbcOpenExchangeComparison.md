## What changed

Retained and checked the two categorical proofs against the current sources.
`WeilConjectures.ZlExchange.fixedPairSupportComparison` constructs the fixed-pair
isomorphism using `IsoAlgebra` and proves its underlying map is exactly `b`.
`WeilConjectures.ZlExchange.pastedExchangeComparison` pastes the two comparison
squares using naturality and the shared middle comparison. The item has one
additional proof-only import, `IsoAlgebraComp`; all statements are unchanged.

The whole item compiled with exit 0 through `lcompile.py` on this resume,
first in 26.5 seconds and then with the current dependency-import baseline in
56.3 seconds. The previously missing public dependency is now published.

## Proved and sorry left

Original holes closed (2 of 7):

- `WeilConjectures.ZlExchange.fixedPairSupportComparison`.
- `WeilConjectures.ZlExchange.pastedExchangeComparison`.

Original holes remaining (5), all under node
`lem-zl-framework-pbc-open-exchange-comparison`:

- `WeilConjectures.ZlFrameworkPbc.openExchangeComparison`.
- `WeilConjectures.ZlFrameworkPbc.diagramNaturality`.
- `WeilConjectures.ZlFrameworkPbc.frameworkOpenRestrictionCoherence`.
- `WeilConjectures.ZlFrameworkPbc.frobeniusWeilSupportComparison`.
- `WeilConjectures.ZlFrameworkPbc.frobeniusWeilSupportComparisonPair`.

No holes added and none split off. Further geometric proof work is in progress.

## No longer needed

No pruning claimed. Retained all current proof-dependency imports, since the
geometric proofs remain unfinished. Removed five stale sandbox dependency copies
from the delivery packet; their shared-source modules remain dependencies.

## Where the brief, the DAG or earlier work was wrong

The earlier missing-publication blocker has cleared. The initial resumed dry run
instead detected one added hole: the retained sandbox copy of
`FlatRingedDiagramRestriction` predated its newly published proof and would
replace that proof with its former `sorry`. Removed this stale copy and the four
unchanged dependency copies, retaining the actual item proofs. The initial gate
reported one minute on a fresh 120-minute reference; the retained report records
many earlier attempts. No budget metadata or launcher files were edited.

The coefficient-square scratch calculation currently exceeds the compile limit;
profiling and localization of its expensive elaboration are in progress. It is
not included in the delivery packet, and the checked item itself compiles.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
