# systemAdjunctionOpenMapShift component theorems

## Reason

The aggregate shift theorem is assembled from three named component theorems so each
remaining proof obligation has an independently tracked DAG node. These public theorem
interfaces are new declarations in the item module and are required by its constructor
proof.

## Old

No component theorem declarations existed in the item module.

## New

`systemAdjunctionOpenMapShift_generators`,
`systemAdjunctionOpenMapShift_adjunctionClauses`, and
`systemAdjunctionOpenMapShift_inverses` are public theorem declarations whose
statements are strict components of `SystemAdjunctionOpenShift`.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.SixFunctors.SystemAdjunctionOpenMapShift` | C1 | Defines and assembles the three components |

## Status

landed 20261027T012816-L-2333801 2026-10-27 (merge of deliver/C1/Sheaf.SixFunctors.SystemAdjunctionOpenMapShift)
