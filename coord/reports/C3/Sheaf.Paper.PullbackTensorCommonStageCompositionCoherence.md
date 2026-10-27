## What changed

Added the finite-stage representative module
`Sheaf.Paper.PullbackTensorCommonStageCompositionFiniteRepresentative` and imported it
from `Sheaf.Paper.PullbackTensorCommonStageCompositionCoherence`. The target theorem now
reduces its common-stage equality to the two representative equalities at one finite
coefficient stage.

## Proved and sorry left

The target declaration `pullbackTensorCommonStageCompositionCoherence` is proved from the
finite-stage representative theorem. The new declaration
`commonStageCompositionFiniteRepresentative` remains `sorry`; it is recorded by node
`lem-pur-pullback-tensor-common-stage-composition-finite-representative`.

## No longer needed

No imports were removed. The target's rational theorem remains a declared dependency for
the finite-stage calculation.

## Where the brief, the DAG or earlier work was wrong

The DAG's one-step proof plan omits the explicit finite-stage representative descent
needed to connect the rational composition equation to the colimit Hom equality. That step
has been split into a separate node.

## New nodes

`lem-pur-pullback-tensor-common-stage-composition-finite-representative` records the
finite coefficient-field calculation and common-stage transport used by the target proof.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PullbackTensorCommonStageCompositionCoherence": "c0051d160e71344224dd4886fa4ed67dd6cb8748", "Sheaf.Paper.PullbackTensorCommonStageCompositionFiniteRepresentative": "f1c39a4578f89585a60093e95e0e8fc1fce0354e"}, "results": {}, "time": "2026-10-28T06:34:24+0800", "transitive": 0, "version": 1}
```

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
