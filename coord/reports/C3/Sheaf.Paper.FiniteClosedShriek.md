## What changed

Closed the top-level `finiteCoefficientClosedShriek` hole by decomposing it into two
strictly smaller, named stage-3 obligations. Added `FiniteClosedShriekMapPart` for the
counit-normalized map, its uniqueness, and the two isomorphism assertions, and added
`FiniteClosedShriekDomainPart` for the three finite-Tor constructibility assertions.
The item imports these proof-only split modules and combines their results by a real
conjunction proof. The other five original theorem holes remain unchanged.

## Proved and sorry left

Closed 1 of 6 original holes: `WeilConjectures.finiteCoefficientClosedShriek`.
The two strict subclaims are currently split obligations with `sorry`:
`WeilConjectures.finiteClosedShriek_mapPart` (node
`lem-coef-closed-shriek-map-part`) and
`WeilConjectures.finiteClosedShriek_domainPart` (node
`lem-coef-closed-shriek-domain-part`).
Five original holes remain in `finiteCoefficientClosedShriek_comp`,
`finiteCoefficientClosedShriek_coefficientChain`,
`finiteCoefficientLocallyClosedShriek`,
`finiteCoefficientLocallyClosedShriek_coefficientChain`, and
`finiteCoefficientLocallyClosedShriek_comp`.

## No longer needed

None. The parent proof uses both new split modules and retains its existing imports.

## Where the brief, the DAG or earlier work was wrong

The parent theorem bundled the normalized-map and finite-Tor-domain arguments into one
unmanageable hole. The proof plan already separates these arguments, so the delivery
records them as strict subclaims and combines them explicitly. No target statement,
definition, or unit route was changed.

## New nodes

`lem-coef-closed-shriek-map-part` records the strict map-normalization and invertibility
subclaim in `Sheaf.Paper.FiniteClosedShriekMapPart`.
`lem-coef-closed-shriek-domain-part` records the strict finite-Tor domain subclaim in
`Sheaf.Paper.FiniteClosedShriekDomainPart`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteClosedShriek": "8ba36df52168445c9b28d7eed8c9dd513f74aab8", "Sheaf.Paper.FiniteClosedShriekDomainPart": "34155f2801cdb7333cfd8e79c5d6592f48e40bf5", "Sheaf.Paper.FiniteClosedShriekMapPart": "243352b058da80dd48e0ce7ac8eb56183e790a3c"}, "results": {}, "time": "2026-10-28T07:19:59+0800", "transitive": 0, "version": 1}
```

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
