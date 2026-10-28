# podReindexing canonical tensor declarations

## Reason
The canonical declarations were moved from the parent module into the descent module so the corrected descent theorem can refer to them without an import cycle. Their names, signatures, bodies, and visibility are unchanged; the parent now publicly imports the descent module.

## Old
`podReindexing_sequence_pullback_eq`, `podReindexingSystemTensor`, `podReindexingIntegralTensorHom`, and `podReindexingIntegralTensorHom_eq` were declared in `Sheaf.Paper.PodReindexingReductionTensorSquare`.

## New
The same declarations are declared in `Sheaf.Paper.PodReindexingReductionTensorSquareDescent`, and the parent publicly imports that module.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.PodReindexingReductionTensorSquare` | F6 / unclaimed in this sandbox | Forced adaptation: declarations are imported from the descent module. |
| `Sheaf.Paper.PodReindexingTensorAugmentationSquare` | downstream | Public names and signatures remain unchanged. |

## Status
landed 20261028T020327-L-2495141 2026-10-28 (merge of deliver/E3/Sheaf.Paper.PodReindexingReductionTensorSquareDescent)
