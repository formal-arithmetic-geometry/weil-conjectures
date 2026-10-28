## What changed

Proved `WeilConjectures.IntegralSystemRealization.properOpenTransportMate_bridge`
in `Sheaf.SixFunctors.IntegralSystemProperOpenTransportBridge` without changing
its statement or its public imports. A private proof import supplies the mate
whiskering and conjugation identities. Two proved private categorical helpers
combine these identities with naturality and inverse/hom cancellation, following
the calculation already present as private helpers in
`AmbientExactClopenComparison`. That module cannot be imported here because it
already reaches this item. Private wrappers and proved normalization equalities
keep derived-functor conversions small; no shared definition or interface changes. The item's DAG proof now
records this calculation.

## Proved and sorry left

Closed the single original hole in
`WeilConjectures.IntegralSystemRealization.properOpenTransportMate_bridge`
(node `lem-sf-integral-system-proper-open-transport-core-bridge-mate`).
The item has zero remaining holes. Added zero holes and split off zero statements.
All private helpers and normalization equalities have complete proofs.

## No longer needed

None. No original imports, dependencies, nodes or modules were removed. The proof
uses the canonical transported mate definition as planned. It does not require
any new mathematical obligation or the intrinsic-mate normalization theorem;
the original public import is preserved for downstream compatibility.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was found. Directly unfolding all four bridge
isomorphisms causes excessive kernel conversion work. Explicit categorical data
and separate normalization equalities avoid that expansion and compile within
the required limit. This closes the obligation rather than splitting it again.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportBridge": "31df1276cd0016369bfcbd3fe5302aebc12ce3fa"}, "results": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportCanonical": {"hash": "a22dc2f1f830b02584b057d67e20ffc8334e4310", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T10:27:51+0800", "transitive": 0, "version": 1}
```

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
