## What changed

Filled `AlgebraicGeometry.Scheme.adicTowerPullback_consecutive_transition_iso`.
The proof constructs the canonical derived scalar-extension/pullback comparison from
`proEtaleRingRestrictionDerivedDirectImage` and composes it with the supplied
`AdicTower.normalization` isomorphism. The etale chart witness is correctly unused by
this tower-only statement.

## Proved and sorry left

Closed the sole sorry, `adicTowerPullback_consecutive_transition_iso`.
No sorry was added.

## No longer needed

The proof does not need any imports beyond `Sheaf.Paper.BoundedConstructibleTower`.
The declared normalization-arrow dependency is used through the existing
`pbcDerivedScalarAdjunction` and pro-etale operations already re-exported by that
module; no separate scalar-realization or constant-sheaf module is needed.

## Where the brief, the DAG or earlier work was wrong

The DAG proof text describes transport through a canonical scalar restriction
comparison but does not name the existing direct-image adjunction API. The supplied
statement is tower-only, so `W` and `_w` do not enter the construction.

## New nodes

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantAdicQuotientRealizationTowerTransition": "c0f829413c96deb69debceb2baf5fd590bc3dca3"}, "results": {"Sheaf.Paper.ConstantAdicQuotientModelRealizationReduction": {"hash": "77cdc9a90937beacc8fbeecd294a581676f3f98a", "status": "OK"}}, "seconds": 127, "time": "2026-10-28T10:31:45+0800", "transitive": 0, "version": 1}
```

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
