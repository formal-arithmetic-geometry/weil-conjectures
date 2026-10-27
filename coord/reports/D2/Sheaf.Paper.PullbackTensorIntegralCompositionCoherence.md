## What changed

`PullbackTensorIntegralCompositionCoherence` now reflects a reduced composition
square through the fully faithful `integralSystemReduction` functor.  I added
`IntegralPullbackTensorCompositionReduced`, whose reduced equality is the
quotient-tower calculation and is left as the next proof item.  The completed
comparison import was removed because this proof does not use it.

## Proved and sorry left

Proved `WeilConjectures.pullbackTensorIntegralCompositionCoherence` from
`integralSystemReduction_fullyFaithful` and the reduced square.  One sorry was
split off in `WeilConjectures.integralPullbackTensorCompositionReduced`, node
`lem-pur-pullback-tensor-integral-composition-reduced`.  No definition contains
`sorry`.

## No longer needed

Removed the proof-only import `Sheaf.Paper.CompletedComparisonQuotientRealization`.
The reduced theorem uses only `DerivedPullbackTensorConstraints` and
`IntegralSystemReductionFullyFaithful`; no other declared proof dependency is
needed by the completed theorem.

## Where the brief, the DAG or earlier work was wrong

The original proof step was stated at the completed integral level, while the
available fully faithful reduction API exposes the natural lower-level boundary.
The delivery makes that boundary explicit: the quotient-system equality is a
strictly simpler statement, and faithfulness is proved directly in Lean.

## New nodes

`lem-pur-pullback-tensor-integral-composition-reduced` records the equality after
`integralSystemReduction`; its source is the finite quotient-tower pure-tensor
calculation in Stacks Tags 07A4 and 0941.  The new declaration is in
`Sheaf.Paper.IntegralPullbackTensorCompositionReduced`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.IntegralPullbackTensorCompositionReduced": "d1e5f24a8666c9ce1593b9d6f968accf1b1ca759", "Sheaf.Paper.PullbackTensorIntegralCompositionCoherence": "91bc7233903b5dd77047a87b82b079efd8f37b7e"}, "results": {"Sheaf.Paper.PullbackTensorCompositionCoherence": {"hash": "d76c6e6b4b555f3c5799a14f929dbdd77b749070", "status": "OK"}, "Sheaf.Paper.PullbackTensorRationalCompositionCoherence": {"hash": "b6afeb0fcc58b3a07a1b8443a979647183b2e295", "status": "OK"}}, "seconds": 17, "time": "2026-10-28T07:19:06+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
