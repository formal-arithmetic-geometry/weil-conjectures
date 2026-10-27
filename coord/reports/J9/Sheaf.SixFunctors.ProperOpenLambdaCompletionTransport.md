## What changed

Proved `properOpenLambdaCompletionTransport` by structural induction on words. The input and unit cases reduce by identity laws, while the tensor, pull, push, and open constructor cases use four strictly smaller named constructor equations. Added one module and DAG node for each constructor equation.

## Proved and sorry left

Closed: `WeilConjectures.OpenInterchangeReduction.properOpenLambdaCompletionTransport`.

Added four split-off sorries, each with its own node: `properOpenLambdaCompletionTransport_tensor`, `properOpenLambdaCompletionTransport_pull`, `properOpenLambdaCompletionTransport_push`, and `properOpenLambdaCompletionTransport_open`.

## No longer needed

None. All four constructor modules are imported by the induction proof, and the ordinary-square module remains required for the statement.

## Where the brief, the DAG or earlier work was wrong

The source implementation contains the recursive transport proof only as a private helper inside a larger module, together with private mate and comparison lemmas unavailable to this module. The assigned module cannot access those private declarations without changing a shared interface. The constructor equations are therefore recorded as strict intermediate statements, and the assigned theorem combines them by a complete induction.

## New nodes

`lem-sf-proper-open-lambda-completion-transport-tensor`, `lem-sf-proper-open-lambda-completion-transport-pull`, `lem-sf-proper-open-lambda-completion-transport-push`, and `lem-sf-proper-open-lambda-completion-transport-open` record the four constructor equations and their remaining proofs.

The interface change is recorded in `coord/changes/proper-open-lambda-completion-transport-constructor-equations.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.ProperOpenLambdaCompletionTransport": "a4e1ee6c34009c9803563236e099b949d40a3922", "Sheaf.SixFunctors.ProperOpenLambdaCompletionTransportOpen": "2f17399ecb361000cc115aac89af9de5f835e6ec", "Sheaf.SixFunctors.ProperOpenLambdaCompletionTransportPull": "ed5da71f667b541aee2015d83983a8895ffc20d7", "Sheaf.SixFunctors.ProperOpenLambdaCompletionTransportPush": "7e54cfe0cae97348f16e5e2e9a2705f3531b17cd", "Sheaf.SixFunctors.ProperOpenLambdaCompletionTransportTensor": "92d0889dd6f44866123ad2f232e1bc79e1ee4098"}, "results": {"Sheaf.SixFunctors.ProperOpenLambdaReductionSquare": {"hash": "f322e69491fd3f45c4e9dac73841eeb0b3d2034d", "status": "OK"}}, "seconds": 27, "time": "2026-10-28T03:55:41+0800", "transitive": 0, "version": 1}
```

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
