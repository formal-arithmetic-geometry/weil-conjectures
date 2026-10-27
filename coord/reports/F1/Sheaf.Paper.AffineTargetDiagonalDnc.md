## What changed

Restored the completed proof of
`WeilConjectures.PurityFiniteSetting.affineTargetDiagonalDnc` from commit
`a60b6d54bdb8efa231e1ba1c59d08840e54e4080` (S4), as required by the return. The proof preserves the theorem signature and all existing
definitions. It adds proof imports of `ChartNormalDifferential`,
`SmoothDiagonalRegularGenerators`, `FiniteSmoothCanonicalInterfaces`, and
`ProEtaleConstantModuleUnit`.

The proof constructs the finite affine cover and chart geometry, proves the
normalized normal-cone/tangent identification and its uniqueness, and constructs
the intrinsic coefficient comparison before applying the stated diagonal
base-change and normalized DNC theorems. The item's DAG proof, dependencies,
and origin match these actual proof steps.

Validation: the restored module compiled alone against the current library with
`lcompile.py`, exit code 0 in 49.2 seconds, with no diagnostic messages.
The prior temporary-filesystem failure did not recur.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurityFiniteSetting.affineTargetDiagonalDnc`
(node `lem-pur-affine-target-diagonal-dnc`). The item now contains zero
`sorry` declarations. No holes were added and no intermediate statements were
split off.

## No longer needed

No imports were removed and no modules or nodes were withdrawn. The proof keeps
the blueprint unit route through smooth base change, diagonal regularity,
diagonal base change, and normalized DNC invariance. The old direct
positive-codimension diagonal interface is not used for the full tangent
normalization, but its public module remains imported and unchanged.

## Where the brief, the DAG or earlier work was wrong

The retained draft stopped at the tangent normalization and intrinsic
coefficient comparison. The completed proof supplies both using the existing
chart-normal-differential, finite-smooth canonical-interface, and intrinsic
coefficient declarations. This is a repair of the returned delivery; the
statement and all public definitions remain unchanged.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
