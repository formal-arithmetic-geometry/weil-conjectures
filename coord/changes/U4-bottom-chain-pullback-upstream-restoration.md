# AlgebraicGeometry.Scheme.bottom_chain_model_pullback_transport

## Reason

Restore the quarantined module assigned by coord/rework.tsv after the 2026-10-20
upstream synchronization. Its archive imports the retired Sheaf derived-pullback
implementation, which collided with the adopted source-library declaration.
Use the current canonical upstream derived pullback. Preserve the entire theorem
signature and existing complete proof. The new derived-pullback implementation
requires a declaration-local heartbeat allowance for elaborating the natural
comparison through several category equivalences; compilation remains within the
60-second wall-clock limit.

## Old

The module is absent from lean/. Its preserved source is
quarantine/Sheaf/AlgebraicGeometry/BottomChainModelPullbackTransport.lean, with:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

The archived theorem has no declaration-local heartbeat override.

## New

Restore lean/Sheaf/AlgebraicGeometry/BottomChainModelPullbackTransport.lean with:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

Precede its existing public theorem and docstring by:

```lean
set_option maxHeartbeats 800000 in
-- The natural comparison crosses module, localized and derived-category equivalences.
```

All declaration signatures, proof bodies, remaining imports and docstrings are
verbatim from the archive. No definition or target statement changes, and no new
mathematical assertion or sorry is introduced. The existing DAG attachment and
proof dependencies are preserved. Targets need no statement re-review due to this
restoration: the assigned repair explicitly reconnects to the already adopted
canonical definition.

## Users

The source-only downstream.py check with --allow-missing and
--uses bottom_chain_model_pullback_transport reports zero live importers/users.
The quarantine and DAG were checked separately; the following archived consumer
still needs this declaration. Its statement and argument order match the restored
signature. It has its own pre-existing stale public import and remains a separate
rework item; restoring this dependency does not change its signature.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport | U4 | restored and compiled |
| Sheaf.AlgebraicGeometry.PerfectUniversalH0TruncationPullback | quarantined; not adapted | existing proof application preserved; requires its own upstream import repair |

No source-library module is changed. No other group's module is adapted.

## Status

landed 20261020T174906-L-816361 2026-10-20 (merge of deliver/U4/Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport)
