# PointSystemTransport public construction extraction

## Reason

The completed finite evaluation proof required the strict-system and finite
construction APIs to compile independently within the stage-3 file limit. Their
signatures and bodies are unchanged; the item publicly re-exports the extracted
modules.

## Old

The declarations from `pointPower` through `transportedDerivedSections`, and from
`coefficient_squares` through `finiteTransportDerived`, were declared in
`Sheaf.Paper.PointSystemTransportDescent`.

## New

Those declarations are declared in `Sheaf.Paper.PointSystemTransportChain` and
`Sheaf.Paper.PointSystemTransportFinite`, respectively, and imported publicly by
`Sheaf.Paper.PointSystemTransportDescent`. All declaration signatures and meanings
are preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointSystemTransportDescent | W4 | public re-export; final evaluation proof |
| Sheaf.Paper.PointSystemNormalizedComparisonData | unclaimed | receives the same declarations through the item |
| Sheaf.Paper.PointRestrictionWholeRoosSquare | unclaimed | receives the same declarations through the item |
| Sheaf.Paper.PointSystemPowerRoosData | unclaimed | receives the same declarations through the item |
| Sheaf.Paper.PointSystemRoosTransportData | unclaimed | receives the same declarations through the item |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | transitive (via PointSystemPowerRoosData); same names, unchanged |
| Sheaf.Paper.PointSystemRoosRestrictionAssembly | unclaimed | transitive (via PointSystemRoosTransportData, PointRestrictionWholeRoosSquare); same names, unchanged |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | transitive (via PointSystemRoosTransportData); same names, unchanged |
| Sheaf.Paper.PointSystemRoosTransportRepresentative | unclaimed | transitive (via PointSystemRoosTransportData); same names, unchanged |

## Status

landed 20261028T020841-L-2553960 2026-10-28 (merge of deliver/W4/Sheaf.Paper.PointSystemTransportDescent)
