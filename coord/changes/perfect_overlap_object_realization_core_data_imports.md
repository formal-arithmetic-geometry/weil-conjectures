# PerfectOverlapObjectRealizationCoreData imports

## Reason

The proof does not use `Mathlib.CategoryTheory.HomCongr` directly; the import is removed during pruning.

## Old

`public import Mathlib.CategoryTheory.HomCongr`

## New

The import is absent.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealization | unclaimed | The parent imports the core module and no longer receives HomCongr transitively. |

## Status

landed 20261014T220652-L-3739426 2026-10-14 (merge of deliver/A4/Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData)
