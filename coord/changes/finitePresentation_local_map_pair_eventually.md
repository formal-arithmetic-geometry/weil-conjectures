# finitePresentation_local_map_pair_eventually
## Reason
The proof now factors through the strictly simpler PairDefectZero statement.
## Old
The theorem was proved directly.
## New
The theorem applies finitePresentation_local_map_pair_eventually_defect_zero and converts the defect to PairCompatibility.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations | F2 | proof continues to use the unchanged target statement |
## Status
landed 20261013T231536-L-1817626 2026-10-13 (merge of deliver/J1/Sheaf.AlgebraicGeometry.FinitePresentationLocalMapPairEventually)
