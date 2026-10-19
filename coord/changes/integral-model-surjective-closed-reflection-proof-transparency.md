# IntegralModelSurjectiveClosedReflection proof transparency attributes

## Reason

The proof adds local irreducibility attributes for the existing upper-star and
module scalar-change definitions. Preflight classifies these commands as a
change to the module's visible environment, so this record documents the
performance and elaboration interface change.

## Old

The module had no local transparency attributes and the theorem body was
`by sorry`.

## New

The proof module contains:

```lean
attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  CondensedRing.upperStarComp upperStarFromPointComp
  Mod.extendScalarsIsoComapInv
```

These attributes are local to this module and preserve every declaration
signature and public definition. They prevent expensive unfolding of the
existing functor definitions while the comparison isomorphisms are assembled.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Imports this module; public declarations and theorem signatures are unchanged. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Publicly imports this module; public declarations and theorem signatures are unchanged. |

## Status

landed 20261019T005419-L-2766383 2026-10-19 (merge of deliver/S3/Sheaf.Paper.IntegralModelSurjectiveClosedReflection)
