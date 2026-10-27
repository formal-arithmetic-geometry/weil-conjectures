## What changed

The parent theorem now assembles three level-specific coherence theorems into its
integral, rational, and common-stage conjunction. Three new modules state the
integral, rational, and common-stage components. The parent proof is complete.

## Proved and sorry left

Proved: `WeilConjectures.pullbackTensorUnitCoherence`.

Sorry left: `WeilConjectures.pullbackTensorIntegralUnitCoherence`,
`WeilConjectures.pullbackTensorRationalUnitCoherence`, and
`WeilConjectures.pullbackTensorCommonStageUnitCoherence`; each is recorded by its
corresponding new DAG node. Three holes were split off from the parent hole.

## No longer needed

No imports or declared dependencies were pruned. The parent now uses only the
three new level-specific declarations; the original direct proof dependencies
are retained by those modules for their eventual proofs.

## Where the brief, the DAG or earlier work was wrong

The direct assembly theorem `DerivedPullbackTensorIso.derivedPullbackTensorIso`
contains the desired conjunction but imports this module, so it cannot be used
as a proof dependency without an import cycle. The obligation therefore had to
be decomposed by coefficient level.

## New nodes

`lem-pur-pullback-tensor-integral-unit-coherence`,
`lem-pur-pullback-tensor-rational-unit-coherence`, and
`lem-pur-pullback-tensor-common-stage-unit-coherence` are the three strict
coefficient-level components of the parent unit-coherence argument. Each has a
named theorem, source note, proof plan, and Lean module in this delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PullbackTensorCommonStageUnitCoherence": "d640c6d3975355a3210b29ddc6bd9d16bc5aa51d", "Sheaf.Paper.PullbackTensorIntegralUnitCoherence": "8e11a6b35cc2a47ceaf506a8b61da8ae94032466", "Sheaf.Paper.PullbackTensorRationalUnitCoherence": "cd6f8e166d0db517d2b24964195bdac764383c89", "Sheaf.Paper.PullbackTensorUnitCoherence": "80f1958454b53c03abd72e2c5dfdf52abe087d96"}, "results": {}, "time": "2026-10-28T02:17:14+0800", "transitive": 0, "version": 1}
```

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
