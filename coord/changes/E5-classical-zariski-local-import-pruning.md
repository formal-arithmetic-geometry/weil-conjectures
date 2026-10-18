# AlgebraicGeometry.ProEtale.proEtaleClassical_zariskiLocal

## Reason

The theorem uses the existing underlying-set classicality predicate and the stronger
set-sheaf local-classicality descent theorem. Its statement needs the continuity-map
module, but no declaration of the module-comparison theorem. Replace that public
import by the module defining the predicate; all theorem binders and the conclusion
remain verbatim unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleClassicalZariskiLocal` reports
zero downstream modules. A library-wide text search finds only this module's own
declaration, so there are no consumers to adapt. No target signature or definition
changes, and no target meaning review is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleClassicalZariskiLocal | E5 | Same theorem signature; narrower public imports. |

## Status

landed 20261018T145058-L-3638295 2026-10-18 (merge of deliver/E5/Sheaf.AlgebraicGeometry.ProEtaleClassicalZariskiLocal)
