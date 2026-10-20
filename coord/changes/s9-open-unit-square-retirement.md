# AlgebraicGeometry.singleComplexOpen_unit_square_factorization

## Reason

Complete the assigned retirement of the quarantined Sheaf copy in favor of its
official upstream twin. Both have exactly the same public theorem statement.
The former Sheaf consumer has already been retired; its upstream replacement
already imports and applies the twin. The item's DAG attachment is still stale.

The rework was checked independently before withdrawal: restore the quarantine
at its assigned sandbox path and remove only the redundant local irreducibility
annotation on `derivedPullback`, which is already globally irreducible. Fresh
remote compilation succeeded without warnings in 23.2 seconds. The unchanged
current upstream consumer compiled in 0.1 seconds. The checked sources remain
under `scratchpad/`, outside the final delivery sources. The quarantine is untouched.

## Old

```text
lean.module: Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization
lean.file: lean/Sheaf/AlgebraicGeometry/SingleComplexOpenUnitSquareFactorization.lean
lean.declaration: AlgebraicGeometry.singleComplexOpen_unit_square_factorization
```

## New

```text
lean.module: WeilConjectures.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization
lean.file: lean/WeilConjectures/AlgebraicGeometry/SingleComplexOpenUnitSquareFactorization.lean
lean.declaration: AlgebraicGeometry.singleComplexOpen_unit_square_factorization
```

The public theorem signature is byte-identical in both sources and the node.
The official twin retains the complete pinned-counit and naturality proof.
The node's proof text now distinguishes the existing global irreducibility of
`derivedPullback` from the two local annotations. Its dependency is unchanged.
`deleted.txt` withdraws the original Sheaf path using the launcher's supported
quarantine-retirement handling. No upstream source or target is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization | absent | Listed former consumer already retired; no adaptation. |
| WeilConjectures.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization | unchanged | Already imports and applies the twin; fresh remote compile passed. |

No live or quarantined Lean module imports the retired Sheaf path. The parent
DAG node `lem-pc-k3-open-counit-homotopy-factorization` already points to the
upstream consumer and continues to depend on the redirected item node. The unit's
statement and proof route stay. Historical creation provenance is not a Lean
dependency and is preserved.

The quarantine, repaired copy, official twin, and checked consumer have zero
textual proof holes. Holes closed: 0; holes added: 0; split off: 0.

## Status

landed 20261020T150706-L-2574567 2026-10-20 (merge of deliver/S9/Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization)
