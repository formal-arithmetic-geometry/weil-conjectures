## What changed

The assigned theorem now composes three explicit comparisons: uniqueness of the prescribed Roos presentation, the canonical global-Hom comparison for the chosen limit, and functorial transport of global Hom along the resulting object isomorphism. Two strictly smaller intermediate theorems were added in separate modules and imported privately by the item. The original theorem signature is unchanged.

## Proved and sorry left

The original theorem `WeilConjectures.integralDualizing_mapping_tower_limit` is proved. The two split obligations remain as named `sorry` theorems:

- `WeilConjectures.integralDualizing_mapping_tower_limit_roos_iso`, node `lem-coef-integral-dualizing-mapping-tower-limit-roos-iso`.
- `WeilConjectures.integralDualizing_mapping_tower_limit_canonical`, node `lem-coef-integral-dualizing-mapping-tower-limit-canonical`.

Thus one hole is closed and two strictly smaller holes are added as a decomposition.

## No longer needed

The original item proof did not use any additional import beyond the mapping-tower construction and the two new split modules. No existing proof-dependency node is pruned; the generic global-Hom/derived-limit comparison is used by the canonical split theorem, and the Roos model is used by the uniqueness split theorem.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof bundled Roos-limit uniqueness, global-Hom transport, and identification with the strict mapping tower into one unproved step. These are separate obligations in Lean. The delivered theorem now combines them by a real isomorphism composition, while the two nontrivial comparisons are stated as strictly smaller public theorems with their own source and proof descriptions.

## New nodes

`lem-coef-integral-dualizing-mapping-tower-limit-roos-iso` records uniqueness of the presented Roos limit and is stated in `IntegralDualizingMappingTowerLimitRoos.lean`.

`lem-coef-integral-dualizing-mapping-tower-limit-canonical` records the canonical global-Hom/strict-mapping-tower comparison and is stated in `IntegralDualizingMappingTowerLimitCanonical.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingMappingTowerLimit": "5c902229735853a11f6d1fdc929f65f328224583", "Sheaf.SixFunctors.IntegralDualizingMappingTowerLimitCanonical": "47c5f7ea9ee438cc4d1e7afc4181d71e670a1cf3", "Sheaf.SixFunctors.IntegralDualizingMappingTowerLimitRoos": "c6feb6a24065354b7245979d004c5b3a1a68556f"}, "results": {"Sheaf.SixFunctors.IntegralDualizingMappingLimitGlobal": {"hash": "367a4fa0e399dfdcb64bb4c9895586c6026e2ea5", "status": "OK"}}, "seconds": 17, "time": "2026-10-28T09:55:27+0800", "transitive": 0, "version": 1}
```

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
