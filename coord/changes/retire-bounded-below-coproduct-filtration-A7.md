# CategoryTheory.exists_boundedBelow_coproduct_filtration

## Reason

The human-authorized retirement row in `coord/retire-items.tsv` assigns the Sheaf
copy to the existing upstream twin. The upstream theorem has the same public
signature and complete proof; retaining both copies would duplicate the notion.

## Old

In `Sheaf.CategoryTheory.BoundedBelowCoproductFiltration`:

```lean
theorem exists_boundedBelow_coproduct_filtration
```

with the full signature recorded by `lem-pc-bounded-below-coproduct-filtration`.

## New

Withdraw `lean/Sheaf/CategoryTheory/BoundedBelowCoproductFiltration.lean` and
attach the node to the existing declaration
`WeilConjectures.CategoryTheory.BoundedBelowCoproductFiltration`.
The declaration name and full theorem signature are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.BoundedBelowCoproductFiltration | A7 | duplicate module withdrawn |
| WeilConjectures.AlgebraicGeometry.TruncatedDirectImageSheafCoproductEpi | unclaimed | already imports the retained upstream twin; no edit required |

## Status

landed 20261021T001103-L-1369201 2026-10-21 (merge of deliver/A7/Sheaf.CategoryTheory.BoundedBelowCoproductFiltration)
