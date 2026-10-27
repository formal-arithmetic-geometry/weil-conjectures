## What changed

The item theorem now assembles two strictly simpler component theorems, one for the
pushforward composite and one for the pullback composite.  The two component modules
are imported proof-only.  Their statements retain the exact corresponding conjunct of
the original target and each has the source paragraph and blueprint tag in its
proof docstring.

## Proved and sorry left

The original `integralKernel_contractions` sorry is closed by a real conjunction
assembly from `integralKernel_first_contraction` and
`integralKernel_second_contraction`.

The two component declarations remain named split-off sorries:

- `integralKernel_first_contraction` in
  `Sheaf.SixFunctors.IntegralKernelFirstContraction`;
- `integralKernel_second_contraction` in
  `Sheaf.SixFunctors.IntegralKernelSecondContraction`.

Each is a strict conjunct of the original statement and has a matching DAG node.
No definition contains a sorry.

## No longer needed

No imports or declared proof dependencies were removed.  The parent node's original
five proof dependencies are represented by the two component nodes, whose statements
are the two required contraction steps.

## Where the brief, the DAG or earlier work was wrong

The existing module had the full contraction theorem as one opaque sorry, while the
available declarations do not expose a proved integral trace/base-change calculation.
The delivery therefore records the two component calculations as the smallest direct
reduction of that conjunction; their proofs remain the next strictly smaller work
items.

## New nodes

`lem-integral-kernel-first-contraction` records the first (pushforward) conjunct and
its source dependencies.

`lem-integral-kernel-second-contraction` records the second (pullback) conjunct and
its source dependencies.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralKernelContractions": "17bfbffcc2e994d2ad929ba87230637d47e5d5ce", "Sheaf.SixFunctors.IntegralKernelFirstContraction": "e243aab527b69dbbed14b7a1fba073c8af426a13", "Sheaf.SixFunctors.IntegralKernelSecondContraction": "217326441cdad0a13645489e36d6b512e326a58f"}, "results": {}, "time": "2026-10-28T03:41:05+0800", "transitive": 0, "version": 1}
```

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
