## What changed

Filled `WeilConjectures.pullbackTensorIntegralBraiding_naturality` in
`Sheaf.Paper.IntegralBraidingNaturality`. The proof defines a local completed tensor
braiding from the existing integral tensor model and strict-system braiding, proves
that its components are the selected integral braiding by the existing uniqueness
normalization, and applies categorical naturality. The module now has only the
statement-bearing public import `Sheaf.Paper.DerivedPullbackTensorConstraints`.

## Proved and sorry left

Closed the sole sorry, `pullbackTensorIntegralBraiding_naturality`. No sorry was
added.

## No longer needed

Removed the proof-only imports `CoefficientRingedSequenceSite`,
`CompletedPullbackTensorComparison`, `ShiftedTensorMorphismCalculus`,
`DerivedPullbackTensorHom`, `CoefDerivedSystemEvaluationCalculus`, and
`IntegralSystemReductionFullyFaithful`; their declarations are not needed directly
because the completed model and braiding interfaces already provide the required
maps. The proof does not use the planned nodes `def-pur-completed-pullback-tensor-comparison`,
`def-coef-ringed-sequence-site`, `lem-coef-derived-system-evaluation-calculus`,
`def-pur-ringed-site-signed-tensor-models`, or
`lem-pod-integral-system-reduction-fully-faithful`.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan expanded the reduction and signed-total calculation even though
the existing completed tensor model exposes a natural isomorphism whose component is
already characterized by the integral braiding uniqueness theorem. No statement or
definition was changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralBraidingNaturality": "1aff23e248dc3fa5a5a484b67fc66abb6b5cbd3d"}, "results": {}, "time": "2026-10-28T08:08:34+0800", "transitive": 0, "version": 1}
```

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
