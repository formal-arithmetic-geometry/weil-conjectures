# AlgebraicGeometry.Scheme.Modules.exteriorSheaf_fullOpen_pushforward_iso

## Reason

Retire the duplicate Sheaf module under the explicit `coord/retire-items.tsv` entry
for `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso`. The retained upstream
module `WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso` already
provides the declaration used by the source consumer.

## Old

The Sheaf module publicly imported `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`
and exported:

```lean
theorem exteriorSheaf_fullOpen_pushforward_iso {X : Scheme.{u}} (M : X.Modules)
    (d : ℕ) :
    Nonempty ((pushforward (⊤ : X.Opens).ι).obj
      (exteriorSheaf ((restrictFunctor (⊤ : X.Opens).ι).obj M) d) ≅
        exteriorSheaf M d)
```

## New

The Sheaf module is withdrawn and replaced by the empty-module landing stub. The
upstream declaration and its public signature remain unchanged in
`WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison | unclaimed | No live Sheaf import; its source counterpart continues using the retained upstream declaration. |

## Status

landed 20261020T233229-L-909046 2026-10-20 (merge of deliver/V4/Sheaf.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso)
