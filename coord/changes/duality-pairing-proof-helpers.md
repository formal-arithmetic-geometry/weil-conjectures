# Sheaf.Paper.DualityPairing proof helpers

## Reason
The standalone symmetry proof uses the opposite-free derived localization
braiding and a concrete presentation of the étale derived tensor. The latter
is isolated as a lower statement because kernel reduction of the concrete
instance exceeds the deterministic isolated compile limit.

## Old
The item had no proof-only helper module and the concrete tensor presentation
was attempted directly in its theorem proof.

## New
`Sheaf.Paper.DualityPairingHelpers` supplies the lower statement
`AlgebraicGeometry.Etale.etaleTensorRaw`; the item contains a private generic
component construction and uses that statement to prove the standalone
symmetry. The helper module is imported proof-only.

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.DualityPairing | F4 | proof-only import and lower statement |

## Status
landed 20261020T211707-L-3489436 2026-10-20 (merge of deliver/F4/Sheaf.Paper.DualityPairing)
