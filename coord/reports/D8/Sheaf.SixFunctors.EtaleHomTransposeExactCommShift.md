## What changed

Added `Sheaf.SixFunctors.EtaleHomTransposeExactCommShiftCore`, whose fixed-degree
`NatTrans.CommShiftCore` calculation is the remaining algebraic step. The assigned
module now assembles these fixed-degree compatibilities with
`NatTrans.CommShift.of_core`. The core theorem remains a named split-off `sorry`.

## Proved and sorry left

The assigned declaration `etaleHomComparison_reversedExact_commShift` is proved from
`NatTrans.CommShift.of_core` and the fixed-degree theorem. One `sorry` remains in
`etaleHomComparison_reversedExact_commShift_core`, at node
`lem-coef-etale-hom-transpose-exact-comm-shift-core`.

## No longer needed

No imports were removed. The direct proof dependency on the tensor-model comparison
is replaced by the fixed-degree core node; the core node records that comparison as
its proof dependency.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan did not expose the fixed-degree shift square as a Lean
statement. The decomposition makes the `CommShift` assembly explicit while leaving
the genuinely separate transpose calculation for proof.

## New nodes

`lem-coef-etale-hom-transpose-exact-comm-shift-core` states the fixed-degree shift
square and is implemented by
`lean/Sheaf/SixFunctors/EtaleHomTransposeExactCommShiftCore.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.EtaleHomTransposeExactCommShift": "8d12cfa535ea2e14e60e3036bf2ccbdb7f998fa2", "Sheaf.SixFunctors.EtaleHomTransposeExactCommShiftCore": "795bd7e078d549efcccb633404fa98f4ebd75287"}, "results": {"Sheaf.SixFunctors.EtaleHomTransposeExact": {"hash": "622f4a341d72fc100afe999c6c8b066086003b43", "status": "OK"}}, "seconds": 80, "time": "2026-10-28T08:02:47+0800", "transitive": 0, "version": 1}
```

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
