# FrobeniusWitnessedCompactification public import repair

## Reason

The completed-refinement proof needs `finite_ring_refinement_coordinates_canonical`.
Its defining module imports `FrobeniusWitnessedCompactification`, whose high-level import
produced the cycle
`QcqsCompletedRefinement -> FiniteRingRefinementCoordinatesCore ->
FrobeniusWitnessedCompactification -> WeilCompactSupportCohomology ->
FieldShriekCompositionQcqs -> FieldShriekCompositionIntegralComponent ->
QcqsCompletedRefinement`.
The witnessed Frobenius module needs `zlFiberMap` from `WeilIndSheafCategory`, but uses
no declarations defined in `WeilCompactSupportCohomology` itself. The lower module has
no import route back to the item.

## Old

`public import Sheaf.Paper.WeilCompactSupportCohomology`

## New

`public import Sheaf.Paper.WeilIndSheafCategory`

No declaration signatures, bodies, visibility, names, attributes or instances change.
This change narrows the transitive public imports of the witnessed Frobenius module.

## Users

Current claim records were checked on the project server. The changed module
`Sheaf.Paper.FrobeniusWitnessedCompactification` is unclaimed.

| Direct importer | Current holder | Effect |
| --- | --- | --- |
| `Sheaf.Paper.FiniteRingRefinementCoordinatesCore` | J1 | Uses the finite-origin API; no source adaptation. |
| `Sheaf.Paper.FiniteRingRefinementCoordinates` | unclaimed | Uses the finite-origin API; no source adaptation. |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | Already publicly imports `WeilCompactSupportCohomology` itself; no source adaptation. |

All three original consumer sources compiled against the changed dependency:
`FiniteRingRefinementCoordinatesCore` in 5.5 s, `FrobeniusSquareExchange` in 41.5 s,
and `FiniteRingRefinementCoordinates` in 4.5 s. Unchanged temporary consumer copies
were removed from the packet afterwards.
No DAG attachment changes are required because no declarations are renamed or moved.

## Status

landed 20261028T020555-L-2525803 2026-10-28 (merge of deliver/M2/Sheaf.Paper.QcqsCompletedRefinement)
