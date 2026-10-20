# AlgebraicGeometry.Scheme.Modules.external_cup_unit_coefficient_identities

## Reason

Retirement item in `coord/retire-items.tsv`, authorized by the human in
`coord/changes/retire-sheaf-twins-20261020.md`, hand-off of October 20.
The duplicate module has zero textual holes. Its upstream twin has the identical
public theorem signature and the same complete proof. The only other declaration
is a local monoidal-category instance; the twin supplies the identical instance.

## Old

```lean
Sheaf.AlgebraicGeometry.ExternalCupUnitCoefficientIdentities
```

The node `lem-sc-external-cup-unit-coefficient-identities` attaches to this duplicate
module and its declaration `AlgebraicGeometry.Scheme.Modules.
external_cup_unit_coefficient_identities`.

## New

```lean
WeilConjectures.AlgebraicGeometry.ExternalCupUnitCoefficientIdentities
```

Withdraw the duplicate through `deleted.txt` and attach the same node to the same
named theorem in the upstream twin. The theorem signature was compared verbatim.
No upstream file, target statement, definition, mathematical dependency, or unit
route changes. No proof or data is replaced by `sorry`.

## Users

The current source has zero importers of the duplicate, confirmed both by `rg`
and `tools/downstream.py`. The retirement inventory's former consumer
`Sheaf.AlgebraicGeometry.PicardExternalCupUnitComparison` is already absent.
Its upstream replacement already imports and uses the upstream twin, and was
compiled successfully with `lcompile.py`.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.AlgebraicGeometry.PicardExternalCupUnitComparison | unclaimed | Already imports the upstream twin; compiled unchanged. |
| WeilConjectures | unclaimed | Already publicly imports the upstream twin; no edit. |

All DAG parents retain their references to the same node and thus the same theorem.
The node attachment is repointed; no node is removed and no dependency is pruned.

## Status

landed 20261020T161733-L-3529417 2026-10-20 (merge of deliver/F3/Sheaf.AlgebraicGeometry.ExternalCupUnitCoefficientIdentities)
