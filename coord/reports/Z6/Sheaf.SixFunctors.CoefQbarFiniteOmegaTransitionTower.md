## What changed

Proved `WeilConjectures.CoefQbarVerdier.finiteOmegaTransition_tower` with its original
statement and public import unchanged. The proof specializes the existing integral
finite-extension u-composition equation, restricts it to constructible objects, and
localizes it. Private categorical transport helpers keep the object equalities and
heterogeneous component normalizations explicit. The existing integral associator
normalization bridge and finite-stage associator specification identify the resulting
comparison with the prescribed rational associator.

Added private proof imports of `CoefIntegralFiniteExtensionComposition`,
`IntegralHomEvaluationNaturality`, and `RationalVerdierIntegralCompNormalization`.
Updated the item's DAG proof and proof dependencies to match these steps.

## Proved and sorry left

Closed the sole original hole in
`WeilConjectures.CoefQbarVerdier.finiteOmegaTransition_tower`.
No sorry remains in the delivered module; no holes or public statements are added.
The proof uses existing declared dependencies, including the integral composition theorem.
The complete module compiled in 24.8 seconds; profiling options were then removed.

## No longer needed

None. The original integral finite-extension composition dependency is retained.
No existing module, node, or import is withdrawn. No new split-off obligation is needed.

## Where the brief, the DAG or earlier work was wrong

The original DAG left the localization calculation unspecified. Its proof now records
all component and object normalizations needed for that calculation. The existing
`RationalVerdier.extension_composition` theorem concerns the duality comparison beta,
so this omega proof uses the u-composition conjunct of the integral theorem instead.
The unit route and all existing public statements and definitions are preserved.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarFiniteOmegaTransitionTower": "3b041dbaf00b21a05f250ba24d0a45de02e49c72"}, "results": {"Sheaf.SixFunctors.CoefQbarFiniteOmegaStageCoherence": {"hash": "94ed9853fdc6ad1f972f690bbbe5115339c9a699", "status": "OK"}}, "seconds": 42, "time": "2026-10-28T11:44:53+0800", "transitive": 0, "version": 1}
```

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
