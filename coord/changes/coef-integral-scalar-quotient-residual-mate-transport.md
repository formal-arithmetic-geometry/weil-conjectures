# WeilConjectures.IntegralFiniteExtension.residual_mate_transport

## Reason
The residual calculation was isolated as a named lower theorem so the assigned core theorem can consume it explicitly.

## Old
No declaration existed.

## New
A public theorem `residual_mate_transport` is added in the assigned module, with the residual mate statement recorded in its DAG node.

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTransposeCore | F2 | The core theorem applies the residual theorem. |

## Status
landed 20261028T034715-L-3536218 2026-10-28 (merge of deliver/C8/Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTransposeCore)
