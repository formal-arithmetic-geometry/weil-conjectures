# ordinaryReducedPull target transport

## Reason

The target proof now imports two proof helpers and composes their natural isomorphisms. The quotient helper exposes the existing finite coefficient comparison, and the projection-model helper isolates the remaining geometric transport.

## Old

`CategoryTheory.ConstantCompletion.ordinaryReducedPull_targetIso` was declared in `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso` with a `sorry` proof and only the source-side public import.

## New

The theorem has the same signature and is proved by composing
`ordinaryReducedPull_targetQuotientIso` and
`ordinaryReducedPull_targetProjectionIso`. The two helper declarations are in new
modules under `Sheaf.Paper`.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation` | unclaimed | imports the target module; its theorem signature is unchanged and its existing proof remains type-correct |

## Status

landed 20261028T020238-L-2484769 2026-10-28 (merge of deliver/C6/Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso)
