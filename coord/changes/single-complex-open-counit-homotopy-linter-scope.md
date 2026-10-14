# AlgebraicGeometry.singleComplexOpen_pullback_counit_homotopy_factorization

## Reason

The original statement includes an unused let binder `F₀`. Its name and signature
are preserved. A completed proof triggers the unused-variable linter for this binder.
The static checker treats the linter command as an interface change, so its scope
is recorded here. No target meaning or mathematical interface changes.

## Old

No unused-variable linter command. The assigned theorem was `:= by sorry`.

## New

`set_option linter.unusedVariables false` is local to the assigned module. It
suppresses the warning about its unchanged statement's `F₀` binder. All existing
public signatures, visibility and public imports are identical. The theorem is
proved by transitivity from the two separate normalization and cancellation steps.
The two new public statements have their own modules and DAG nodes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization | M3 | Local lint checking only |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitRepresentative | unclaimed in supplied snapshot | No adaptation |

All transitive importers see the same original interface. No other module is edited.

## Status

landed 20261014T054053-L-2107491 2026-10-14 (merge of deliver/M3/Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization)
