## What changed

Filled the sole proof hole in `Sheaf.Paper.AmbientCoefficientPullbackFiniteIso`, proving
`WeilConjectures.AmbientPullbackTensor.coefficientPullback_some_isIso`. The proof compares
the chosen ringed-site adjunction with the constant-sheaf adjunction at the pro-etale
terminal object. Uniqueness of left adjoints identifies the defined `ringMap` with the
component of this comparison, which is an isomorphism. No imports or public signatures
changed.

## Proved and sorry left

Closed the existing `coefficientPullback_some_isIso` sorry. The item module has zero
remaining sorries and the delivery adds no sorries.

## No longer needed

No imports, nodes, or modules were removed. The proof uses the existing
`lem-sf-ambient-pullback-site-constructions` dependency through
`Sheaf.Paper.AmbientPullbackSiteData`; no additional dependency was needed.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was accurate. The direct constant-sheaf adjunction argument gives the
finite-stage comparison without introducing an intermediate theorem or changing any
statement.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AmbientCoefficientPullbackFiniteIso": "a69cfe46c275643fac5132a4f433e474418df702"}, "results": {}, "time": "2026-10-28T09:24:06+0800", "transitive": 0, "version": 1}
```

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
