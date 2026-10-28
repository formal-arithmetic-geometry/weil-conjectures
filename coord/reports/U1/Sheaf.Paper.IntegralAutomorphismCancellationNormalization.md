## What changed

Added the private proof imports needed for the stated cancellation interface and proved
the target by cancelling the composite of the two invertible kappa comparisons. The
precomposition calculation is isolated as the strictly simpler theorem
`integralAutomorphismCancellation_precomposition` in a new module.

## Proved and sorry left

Closed: `WeilConjectures.integralAutomorphismCancellation_normalization` (one original
hole). Added one named split theorem: `WeilConjectures.integralAutomorphismCancellation_precomposition`.

## No longer needed

The representative-level whole-system dependencies from the original plan are not
separately used by the parent after the precomposition split. No existing library
module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The target statement is unchanged. The original DAG proof described the full
representative calculation in one node; the proof is reduced to its precomposition
part followed by an explicit epimorphism cancellation.

## New nodes

`lem-sf-integral-automorphism-cancellation-precomposition` records the split theorem
and its source proof plan. Its proof is left for a subsequent stage-3 worker.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralAutomorphismCancellationNormalization": "d5c94cc700c1e1f8374f3a7fa0fc82f06f8415c9", "Sheaf.Paper.IntegralAutomorphismCancellationPrecomposition": "9b2feabaf8d8965c2964fd7a78ff598a08650d36"}, "results": {"Sheaf.Paper.AutomorphismConstructibleStageEquivalence": {"hash": "b592d0ba95d72ba45e89d10d2b8b24b79e82e7e2", "status": "OK"}}, "seconds": 65, "time": "2026-10-28T08:18:30+0800", "transitive": 0, "version": 1}
```

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
