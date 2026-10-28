## What changed

Proved `WeilConjectures.automorphismSquareStageCompatibility` with its original signature.
Added proof-only imports of `Sheaf.Paper.NormalizedIntegralMixedCoherence` and
`Sheaf.Paper.IntegralScalarPullbackCompletionNormalization`.
The proof first cancels the integral compositors, identifies the scalar maps by
normalization, rationalizes the resulting equality, and conjugates by the stage
transition isomorphisms. All intermediate helpers are private and proved.
The localization calculation adapts the existing proved calculation in the downstream
`AutomorphismSquareRationalScalar` module; importing that module would create a cycle.
Updated the item's DAG proof and proof origin to describe the implemented argument.

## Proved and sorry left

Closed the one existing hole in `WeilConjectures.automorphismSquareStageCompatibility`
(node `lem-sf-automorphism-square-stage-compatibility`). No holes added, none left.

## No longer needed

None. All four original proof dependencies are used, and both original public imports
remain. No module or node is withdrawn; the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The DAG's elementary rationalization step
requires explicit heterogeneous endpoint transport because the chosen rational functors
have propositional rather than definitional object formulas. This is now proved in
private helpers, without adding new obligations or changing any public definition.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AutomorphismSquareStageCompatibility": "26285d79d2ab6859cf74c65b534da29f51bf1d1a"}, "results": {"Sheaf.Paper.AutomorphismConstructibleStageEquivalence": {"hash": "6bb9c8c0d6798dcfc3e0fbaff2197351364de4e0", "status": "OK"}}, "seconds": 257, "time": "2026-10-28T14:24:30+0800", "transitive": 0, "version": 1}
```

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
