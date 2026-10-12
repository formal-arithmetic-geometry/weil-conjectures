# AlgebraicGeometry.Scheme.Modules.H.globalFreeExtComparison

## Reason
The proof adds local helper declarations and uses `open Opposite`; the static
stage-3 check classifies this as an externally visible environment change.

## Old
```lean
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
```

## New
```lean
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
open Opposite
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisGlobalExtComparison | H2 | proof elaboration only |

## Status
landed 20261012T160827-L-2611351 2026-10-12 (merge of deliver/H2/Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisGlobalExtComparison)
