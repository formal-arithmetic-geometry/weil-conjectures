# AlgebraicGeometry.ProjectiveSpace.ι_homOfIsFreeGenerator_reindex

## Reason
The main proof needs a named chart restriction theorem. It is a strictly smaller public result, and the item imports its module for the proof.

## Old
No declaration existed.

## New
The module `Sheaf.AlgebraicGeometry.ProjectiveSpaceReindexChart` declares `ι_homOfIsFreeGenerator_reindex`, identifying the restriction of the reordered projective-space morphism with affine coordinate reindexing on every standard chart.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProjectiveSpaceReindexIsIso | C3 | imports and applies the chart theorem |

## Status
landed 20261012T124146-L-1155887 2026-10-12 (merge of deliver/C3/Sheaf.AlgebraicGeometry.ProjectiveSpaceReindexIsIso)
