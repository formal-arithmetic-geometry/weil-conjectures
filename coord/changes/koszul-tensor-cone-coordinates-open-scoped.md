# Koszul tensor cone proof scope commands

## Reason

The proof uses tensor-product notation and requires the `TensorProduct` scoped notation in the
module. The scope command is visible to later importers, so it is recorded explicitly.

## Old

`Sheaf.RingTheory.KoszulTensorConeCoordinates` had no `open scoped TensorProduct` command.

## New

The proof module contains `open scoped TensorProduct` so its tensor-product expressions elaborate.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.RingTheory.RegularSequenceKoszulRegular` | unclaimed | downstream imports the theorem; its existing notation is unaffected |

## Status

landed 20261012T173851-L-3302331 2026-10-12 (merge of deliver/P3/Sheaf.RingTheory.KoszulTensorConeCoordinates)
