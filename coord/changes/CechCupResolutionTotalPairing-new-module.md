# AlgebraicGeometry.Scheme.Modules.cupCechResolution_total_pairing

## Reason

The assigned module and declaration are absent from the current sheaf-dag baseline. This
repair retains the unchanged target-facing signature and supplies its compiled proof.
The comparison-data dependency is already landed and is not modified.

## Old

No declaration in the baseline module system.

## New

The module `Sheaf.Paper.CechCupResolutionTotalPairing` declares
`cupCechResolution_total_pairing` with the unchanged signature recorded in
`lem-sc-cech-cup-resolution-total-pairing`. Its proof transports the characterized sheaf
cup product through the three comparison isomorphisms and uses the separately stated beta
axis obligation.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CechCupResolutionTotalPairing | M4 | restored module uses the delivered beta-axis theorem |

A repository-wide search finds no current baseline Lean importer or declaration user of
either restored module. The table records the dependency within this delivery;
there are no existing consumer modules to adapt. Both signatures are byte-for-byte
unchanged from the files in repair record `ebf9d37306c806a6`.

## Status

landed 20261013T222406-L-1224042 2026-10-13 (merge of deliver/M4/Sheaf.Paper.CechCupResolutionTotalPairing)
