# FiniteThickeningCartesian imports

## Reason
The proof does not use `Sheaf.AlgebraicGeometry.BaseChangeConventions` or the
universal-homeomorphism module. The former was a public import visible to the
item's importer; removing it keeps the module interface minimal. The latter was
already proof-only and is removed from the proof imports.

## Old
```lean
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
```

## New
```lean
-- neither import is present
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteEtaleThickeningLift | unclaimed | It imports `FiniteThickeningCartesian`; no declaration or statement from `BaseChangeConventions` is mentioned, so its elaborated interface is unchanged. |

## Status
landed 20261012T135317-L-1692992 2026-10-12 (merge of deliver/T2/Sheaf.AlgebraicGeometry.FiniteThickeningCartesian)
