# CategoryTheory.roosPrefixFunctor

## Reason

The resolution needs explicit finite-prefix functors and product limit cones. The existing
surjective-tower acyclicity module cannot be imported here without an import cycle.

## Old

No declarations or modules named `RoosFinitePrefixes`, `RoosFinitePrefixLimits`, or
`RoosPrefixAcyclic` existed. Every existing declaration signature is preserved.

## New

New public declarations are recorded verbatim in the three accompanying nodes' Lean
records. In particular:

```lean
def roosPrefixFunctor (s : ℕ) :
    (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{u})
```

Its explicit prefix data and natural maps are in `RoosFinitePrefixes`. The proved
product limit cone is in `RoosFinitePrefixLimits`. The only unproved theorem is
`roosPrefixAcyclic`, vanishing of positive derived limits on these explicit towers.
The item imports the last two modules privately. No existing public interface or target
statement changes, and no module needs a forced adaptation.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.RoosAcyclicResolution | P3 | privately imports the proof helpers |
| Sheaf.CategoryTheory.RoosFinitePrefixLimits | new in this delivery | prefix limit cone |
| Sheaf.CategoryTheory.RoosPrefixAcyclic | new in this delivery | prefix acyclicity statement |

These new names have no existing users; existing downstream modules see the same item
interface. There are no adaptations of held or unclaimed existing modules.

## Status

landed 20261012T163617-L-2786473 2026-10-12 (merge of deliver/P3/Sheaf.CategoryTheory.RoosAcyclicResolution)
