# Proper/open lambda completion transport constructor equations

## Reason

The assigned transport proof uses four strictly smaller constructor equations. They are public declarations in new modules so the remaining recursive proof is explicit and reviewable.

## Old

The assigned module contained only the public theorem `properOpenLambdaCompletionTransport` with a `sorry` proof.

## New

The assigned module proves `properOpenLambdaCompletionTransport` by structural induction and imports four new constructor modules. Those modules state the tensor, pull, push, and open constructor equations, each with a named `sorry` proof and matching DAG node.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.SixFunctors.ProperOpenLambdaReductionSquare` | Y9 | imports the assigned theorem; now receives its inductive proof |
| `Sheaf.SixFunctors.ProperOpenLambdaCompletionTransport` | J9 | imports and combines the four constructor equations |

## Status

landed 20261027T210112-L-1656002 2026-10-27 (merge of deliver/J9/Sheaf.SixFunctors.ProperOpenLambdaCompletionTransport)
