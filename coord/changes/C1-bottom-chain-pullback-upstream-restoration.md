# AlgebraicGeometry.Scheme.bottom_chain_model_pullback_transport

## Reason

Restore the quarantined module assigned by `coord/rework.tsv` after the upstream
synchronization. The archive imported a retired Sheaf `derivedPullback`, which collided
with the adopted source-library declaration. Reconnect the proof to the canonical
upstream implementation while preserving its theorem interface and complete proof.

## Old

The module was absent from `lean/`. Its preserved source imported:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

and had no declaration-local heartbeat override.

## New

The restored module imports:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

and places the existing theorem under:

```lean
set_option maxHeartbeats 800000 in
-- The natural comparison crosses module, localized and derived-category equivalences.
```

The declaration signature, docstring, proof body, and all other imports are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport` | C1 | restored and compiled |
| `Sheaf.AlgebraicGeometry.PerfectUniversalH0TruncationPullback` | quarantined; unclaimed | existing consumer remains quarantined with its own stale import and is not adapted |

The source-only downstream scan reports no live importers in `lean/`; the quarantined
consumer is preserved separately and matches the restored theorem's argument order.

## Status

landed 20261020T221058-L-4141496 2026-10-20 (merge of deliver/C1/Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport)
