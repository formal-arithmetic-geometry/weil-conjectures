# Sheaf.Paper.ExceptionalRingTransportCore imports

## Reason
The core proof now obtains its transport subpackages through the new post-data module,
which transitively exposes the scalar-mates declarations.  The direct public import of
`Sheaf.Paper.ExceptionalIntegralScalarMates` is therefore redundant and was removed.

## Old
```lean
public import Sheaf.Paper.ExceptionalIntegralScalarMates
```

## New
```lean
public import Sheaf.Paper.ExceptionalRingTransportCorePostData
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ExceptionalRingTransportCoreLaws | unclaimed | Compiles through the new public post-data import. |

## Status

landed 20261027T233948-L-4143113 2026-10-27 (merge of deliver/G6/Sheaf.Paper.ExceptionalRingTransportCoreData)
