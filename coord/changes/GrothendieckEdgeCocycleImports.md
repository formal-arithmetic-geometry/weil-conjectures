# GrothendieckEdgeCocycle public imports

## Reason

The declaration only needs the composable-pair and decreasing-filtration APIs.
The Cartan--Eilenberg double-complex model was exported as a statement dependency
although no name from that model occurs in the theorem's type. Export the two
actual statement dependencies directly. No declaration signature or definition changes.

## Old

```lean
public import Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel
```

## New

```lean
public import Sheaf.CategoryTheory.GrothendieckComposablePair
public import Sheaf.CategoryTheory.Filtration
import Sheaf.CategoryTheory.GrothendieckCocycleComparison
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.LerayEdgeCocycleData | unclaimed in the local snapshot | Uses the unchanged cocycle theorem; no double-complex model declaration occurs in its statement or proof. |
| Sheaf.AlgebraicGeometry.LerayEdgeVanishingIso | unclaimed in the local snapshot | Uses the unchanged collapse clause; no double-complex model declaration occurs in its statement or proof. |

The read-only import-pruning check found no downstream use of declarations that
would become inaccessible. Both current direct importers were checked against the
sandbox modules. The current snapshot has 444 downstream modules through these
two importers; their statements and definitions are untouched. The first worker's
snapshot had LerayDegenerateSections as the sole direct importer, before its split.

## Status

landed 20261012T070544-L-3474530 2026-10-12 (merge of deliver/N2/Sheaf.CategoryTheory.GrothendieckEdgeCocycle)
