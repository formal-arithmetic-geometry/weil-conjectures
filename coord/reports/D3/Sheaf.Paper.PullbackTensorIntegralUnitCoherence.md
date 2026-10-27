## What changed

Added proof-only imports for two strictly smaller obligations and closed
`WeilConjectures.pullbackTensorIntegralUnitCoherence` by combining their
existence and uniqueness results. The assigned theorem now has no `sorry`.

## Proved and sorry left

The assigned declaration `pullbackTensorIntegralUnitCoherence` is proved. Two
strictly simpler declarations remain as deliberate stage-3 splits:
`canonicalIntegralPullbackTensor_unit_exists` in
`lem-pur-pullback-tensor-integral-unit-coherence-existence`, and
`canonicalIntegralPullbackTensor_unit_unique` in
`lem-pur-pullback-tensor-integral-unit-coherence-uniqueness`.

## No longer needed

No imports or declared dependencies were removed. The parent constraints module
remains needed by both split obligations.

## Where the brief, the DAG or earlier work was wrong

The parent module exposes the normalized system unit construction and coherent
reduction infrastructure, but does not expose the reduction naturality lemmas
needed to complete the integral existence and cancellation calculations in this
item. The delivery therefore records those two genuinely smaller proof steps as
named obligations rather than hiding them inside the assigned theorem.

## New nodes

`lem-pur-pullback-tensor-integral-unit-coherence-existence` records the existence
half, sourced from Stacks Tag 07A4 and using the parent normalized constraints.
`lem-pur-pullback-tensor-integral-unit-coherence-uniqueness` records the
cancellation uniqueness half, with the same source and parent dependency.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PullbackTensorIntegralUnitCoherence": "3d4ebd50f7e09972fa743a624fe135508a855687", "Sheaf.Paper.PullbackTensorIntegralUnitExistence": "5c50ef8cd8597429494c415aa7c430c0c2fb66dd", "Sheaf.Paper.PullbackTensorIntegralUnitUniqueness": "def5d37d468aa8895b9fab8cff63c94eaaee3eb4"}, "results": {}, "time": "2026-10-28T06:34:10+0800", "transitive": 0, "version": 1}
```

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
