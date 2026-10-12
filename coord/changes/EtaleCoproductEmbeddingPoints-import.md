# EtaleCoproductEmbeddingPoints import visibility

## Reason
`Mathlib.AlgebraicGeometry.Limits` is already available through the public imports
of `EtaleFieldPointFunctor`. Removing its redundant explicit import preserves both
the theorem signature and the available public declarations; the proof and its
unchanged direct importer compile against this removal.

## Old
`public import Mathlib.AlgebraicGeometry.Limits`

## New
The redundant explicit import is removed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleFieldPointFunctorEssSurj | unclaimed | Compiles unchanged against the delivered module; Mathlib.AlgebraicGeometry.Limits remains available through EtaleCoproductOfFiniteSeparableFields; no adaptation required. |

## Status
landed 20261012T161501-L-2647743 2026-10-12 (merge of deliver/J1/Sheaf.AlgebraicGeometry.EtaleCoproductEmbeddingPoints)
