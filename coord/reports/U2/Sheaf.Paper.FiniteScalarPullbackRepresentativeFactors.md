## What changed

Added the local left-derived factor-counit helper and imported the exact-derived factorization APIs. The paper-level representative-factor theorem is proved by reducing its wrappers to the expanded derived mate normalization theorem. The expanded theorem is split off as a named intermediate statement for parallel proof.

## Proved and sorry left

Proved `WeilConjectures.finiteScalarPullback_representative_factors`.

Left `WeilConjectures.finiteScalarPullback_representative_factors_core` as one split-off sorry, with DAG node `lem-sf-finite-scalar-pullback-representative-factors-core`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original module's proof plan omitted the concrete expanded mate-normalization statement needed to connect the generic exact-derived mate API to the paper-level wrappers; this delivery records that missing step as a new node.

## New nodes

`lem-sf-finite-scalar-pullback-representative-factors-core` is the expanded derived-category mate equation used by the proved wrapper theorem.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteScalarPullbackRepresentativeFactors": "92dd83c2e2c4712d921b57df1390ea810ff16aea"}, "results": {"Sheaf.Paper.FiniteScalarFixedTensorPullbackNormalization": {"hash": "7020a6e34ce9b057934074a764c7138e0962a8a7", "status": "OK"}}, "seconds": 53, "time": "2026-10-28T06:40:25+0800", "transitive": 0, "version": 1}
```

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
