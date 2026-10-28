## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerClasses.integral_site_pullback_units_endpoint_canonical`
in `Sheaf.Paper.IntegralSitePullbackUnitsEndpointCanonical`, preserving its statement and all
existing public imports. Added the proof-only import
`WeilConjectures.WeilSheaf.FieldCoefficientTateTwist` for its already proved generic
`CategoryTheory.conjugateIsoEquiv_symm_hom_app_comp_map_comp`.

After cancellation of the inverse comparison, the generic lemma reduces the endpoint square
to a square of direct-image maps. The three adjunction definitions reduce this to pullback of
units along the same first projection. The concrete chartwise calculation is complete.
Updated the item's DAG proof and proof origin to describe this argument.

Validation: the module compiles cleanly with `lcompile.py` in 7.0 seconds. The import-direction
check permits the additional proof import. No statements, definitions, instances, attributes,
or public imports changed. No other existing modules require adaptation.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.SpTowerClasses.integral_site_pullback_units_endpoint_canonical`
(node `lem-sp-integral-site-pullback-units-endpoint-canonical`).
Added 0 holes; split off 0 statements. No `sorry` remains in the item module.
This is a complete proof using the existing general adjoint-square lemma, with no new
unproved endpoint or mate lemma.

## No longer needed

None. No imports removed and no dependency nodes or modules pruned. All four original
proof dependencies remain used. No new module or node was introduced.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan was correct. The existing partial proof expanded the conjugate and
passed to chartwise extensionality while adjunction units and counits still remained.
Using the existing general adjoint-square lemma performs those cancellations before the
chartwise calculation. The current server queue lists a one-hole proof item and has no
build-error or rework entry for this module.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralSitePullbackUnitsEndpointCanonical": "5a8715e53cd2bb9bc5033cd229306b66f19a42e0"}, "results": {}, "time": "2026-10-28T09:19:35+0800", "transitive": 0, "version": 1}
```

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
