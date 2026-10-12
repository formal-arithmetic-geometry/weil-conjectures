# Mathlib.CategoryTheory.Preadditive.Injective.Preserves import visibility

## Reason

The module uses this import only while proving mono preservation. It is not needed by
any public statement or definition, so it must be a proof-only import under the stage-3
module contract.

## Old

`public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves`

## New

`import Mathlib.CategoryTheory.Preadditive.Injective.Preserves`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Sites.OverPullbackAdjunctionMono | P3 | compiles unchanged; proof-only dependency is private |
| Sheaf.CategoryTheory.Sites.OverPullbackPreservesInjectives | unclaimed | Direct importer; explicitly imports Mathlib.CategoryTheory.Preadditive.Injective.Preserves and compiles unchanged against the delivered module. |

## Status

landed 20261012T212210-L-1098108 2026-10-12 (merge of deliver/P3/Sheaf.CategoryTheory.Sites.OverPullbackAdjunctionMono)
