## What changed

Proved `pairingCancellation` by applying the generic categorical cancellation lemma
`CategoryTheory.cancelMappedPairing` to the scalar-extension and star functors. The
remaining normalization from `PairingChangeEquation` is isolated in the new module
`Sheaf.Paper.LocallyClosedPairingEquationExpansion`.

## Proved and sorry left

Closed the `pairingCancellation` hole. Added one strictly smaller normalization
statement, `pairingEquation_expanded`, whose proof remains `sorry` (node
`lem-coef-locally-closed-pairing-equation-expansion`).

## No longer needed

No imports or proof dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG step treated unfolding and reassociation of `PairingChangeEquation`
as immediate. In this environment, elaborating that conversion directly exceeds the
single-file time limit, so it is isolated as a separately named normalization step.

## New nodes

`lem-coef-locally-closed-pairing-equation-expansion` records the explicit expansion
needed by the cancellation proof and is declared in
`lean/Sheaf/Paper/LocallyClosedPairingEquationExpansion.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.LocallyClosedPairingCancellation": "01840b87b63c3da67aaa55aae6a9533cf7b590f6", "Sheaf.Paper.LocallyClosedPairingEquationExpansion": "2382e51dfbdcc67aa513b2c528fa421959ed0663"}, "results": {}, "time": "2026-10-28T02:06:55+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
