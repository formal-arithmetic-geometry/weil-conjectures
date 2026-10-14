# AlgebraicGeometry.Scheme.Modules.cupCechResolution_total_pairing

## Reason

Restore the absent total-pairing module with its original signature. The previous
beta-class companion and the untracked signed-axis module are unnecessary. Use the
tracked total cochain morphism and a general homology descent lemma instead.

## Old

The total-pairing module is absent in the delivery baseline after rollback.

## New

The theorem signature recorded in
`dag/nodes/sec-abelian-varieties/lem-sc-cech-cup-resolution-total-pairing.json`
is preserved verbatim. Its proof uses the existing total cochain pairing theorem,
component-wise comparison map equalities, and naturality of cycle classes.
The new general descent theorem has no sheaf or comparison-map assumptions.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CechCupResolutionTotalPairing | M2 | Restored original theorem. |

No tracked baseline module imports either absent total-pairing or beta-class module.
No existing module is adapted; no target statement or definition changes.

## Status

landed 20261014T074216-L-3520607 2026-10-14 (merge of deliver/M2/Sheaf.Paper.CechCupResolutionTotalPairing)
