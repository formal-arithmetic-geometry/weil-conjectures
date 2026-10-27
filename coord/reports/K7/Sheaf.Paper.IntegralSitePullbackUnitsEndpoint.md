## What changed

Added the canonical units endpoint module and imported it as a proof-only dependency.
The item theorem now identifies the arbitrary map `a` with
`towerIntegral_unitsSheafPull f` by adjunction injectivity and the chartwise
`towerIntegral_unitsPull_adjoint` formula, then applies the canonical endpoint
statement. Updated the item DAG proof route and added the split node for the
canonical specialization.

## Proved and sorry left

Closed `integral_site_pullback_units_endpoint`.
The added theorem `integral_site_pullback_units_endpoint_canonical` remains a
single named `sorry` in node
`lem-sp-integral-site-pullback-units-endpoint-canonical`; it is the strictly
simpler fixed-map mate calculation used by the proved theorem.

## No longer needed

None. All original imports remain needed by the statement or proof; the two
added imports supply the canonical units map and its endpoint substatement.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan omitted the canonical-map reduction. The
chartwise hypothesis first determines `a` uniquely as the adjoint of
`unitsDirect`; the remaining comparison square is a separate fixed-map mate
calculation. That calculation is recorded as a split node rather than being
repeated under the arbitrary hypotheses.

## New nodes

`lem-sp-integral-site-pullback-units-endpoint-canonical` in
`dag/nodes/sec-smooth-purity/lem-sp-integral-site-pullback-units-endpoint-canonical.json`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralSitePullbackUnitsEndpoint": "69f544d99c7a7b86315af4c2251efc92c510e1fd", "Sheaf.Paper.IntegralSitePullbackUnitsEndpointCanonical": "b33207e9e0de5ce0cd5c6bd5272e8f9a5f9291d0"}, "results": {}, "time": "2026-10-28T05:35:35+0800", "transitive": 0, "version": 1}
```

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
