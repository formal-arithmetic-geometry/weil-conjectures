## What changed

The target proof now applies a finite quotient stage theorem and a joint-faithfulness
(extensionality) theorem for coherent integral-system reduction.  Two new Sheaf modules
state those strictly smaller steps and are imported privately by the target module.
The target theorem's statement and its public imports are unchanged.

## Proved and sorry left

The target declaration `WeilConjectures.integralPullbackTensorCompositionReduced` is
proved from the two split statements.  The delivery adds the named sorries
`WeilConjectures.integralPullbackTensorCompositionReduced_finiteStage` and
`WeilConjectures.integralSystemReduction_map_ext`; each is a public theorem with a
DAG node and a proof plan.  Thus one existing sorry is closed and two strictly smaller
sorries are added as a decomposition.

## No longer needed

No existing proof dependency or import was removed.  The proof uses the two new
modules and retains the declared quotient-realization and integral-composition
dependencies.

## Where the brief, the DAG or earlier work was wrong

The original node's single proof step hid both the finite-stage pure-tensor calculation
and the joint-faithfulness passage from all quotient levels to the derived system.  They
are now explicit new nodes so that the remaining work is stated independently.

## New nodes

- `lem-pur-pullback-tensor-integral-composition-reduced-finite-stage`: finite-stage
  equality after every coefficient evaluation.
- `lem-pur-integral-system-reduction-map-ext`: joint faithfulness of the quotient
  evaluations after coherent integral reduction.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralPullbackTensorCompositionReduced": "1ae82b80992d4412acd53bd91e60b963840ee7f4", "Sheaf.Paper.IntegralPullbackTensorCompositionReducedFiniteStage": "6a6c3518f42bb688a0a58d5f3300213c4c3175bc", "Sheaf.Paper.IntegralSystemReductionMapExt": "6008dd587e150676c9f4ef27dd5bbc87133e8d4e"}, "results": {}, "time": "2026-10-28T07:58:30+0800", "transitive": 0, "version": 1}
```

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
