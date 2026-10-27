## What changed

Added the proof-only import `Sheaf.Paper.SystemOpenScalarEvaluationCore`. The assigned
forward evaluation theorem is now proved by applying the inverse-mate evaluation square
and cancelling the evaluated inverse/forward pair. The new core module states the strict
inverse-mate substep and leaves only that substep as a named `sorry`.

## Proved and sorry left

Closed `WeilConjectures.FrobeniusExchange.systemOpenScalar_finiteEvaluation` (1 of 1
sorries in the assigned module). Added one strictly lower-level statement, with the
only remaining hole in
`WeilConjectures.FrobeniusExchange.systemOpenScalarInv_finiteEvaluation_core` in
`Sheaf.Paper.SystemOpenScalarEvaluationCore`.

## No longer needed

None. The assigned module's original imports remain needed for its public definitions and
for the inverse-mate core. No declared DAG dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof text described the inverse-mate calculation but did not expose its
required equation as a separately stated lower-level obligation. The delivery adds that
strict inverse-mate node and proves the parent by a concrete cancellation calculation.

## New nodes

`lem-sf-system-open-scalar-evaluation-core` states the inverse-mate evaluation square,
which omits the forward `systemOpenScalar` component and is therefore strictly below the
assigned theorem. Its Lean declaration is in
`lean/Sheaf/Paper/SystemOpenScalarEvaluationCore.lean`; its proof is sourced from Zheng
Construction 4.1 and Lemma 4.10 and Stacks 03DI/07A6, with the exact inverse-mate
calculation recorded in the declaration docstring.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.SystemOpenScalarEvaluation": "049ad19fc6b6b03152b195e99050b53438e9f396", "Sheaf.Paper.SystemOpenScalarEvaluationCore": "c45132e368ae45d5977f5df7e92d69c891c095dc"}, "results": {"Sheaf.Paper.CompactSupportScalarEvaluationSquare": {"hash": "4873c6b3e3219cb09a4e30281962b19eb1d15711", "status": "OK"}}, "seconds": 31, "time": "2026-10-28T03:58:08+0800", "transitive": 0, "version": 1}
```

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
