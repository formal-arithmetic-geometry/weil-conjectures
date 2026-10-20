# AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_directImages

## Reason

Restore the quarantined module assigned in `coord/rework.tsv`. After the upstream sync,
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` is an empty withdrawn
module. The theorem statement uses `externalCupCoefficients`, which its other imports
expose only privately. Import the canonical adopted source module publicly.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The full original module is preserved at
`quarantine/Sheaf/AlgebraicGeometry/PicardExternalCoefficientsDirectImages.lean`.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

This single replacement restores the module at its original Lean path. All declaration
signatures, proof bodies, attributes, definitions and other imports are unchanged.
No target statement or definition meaning changes, so no target review is reopened.
The restored module compiles without errors or warnings through `lcompile.py` (9.2 s).

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsDirectImages | G3 | Restored with the canonical public statement dependency. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAcyclic | unclaimed, quarantined | The same theorem and signature are available again; no adaptation is forced by this repair. |

`tools/downstream.py` reports the module as unknown because it is quarantined.
Searching both `lean/` and `quarantine/` for its import and theorem finds only the
quarantined acyclicity consumer above. Its independent stale field-linear import
predates this repair. No consumer changes are included. The existing DAG attachment,
proof dependencies, parent edges and unit route are preserved.

## Status

landed 20261020T154044-L-3035070 2026-10-20 (merge of deliver/G3/Sheaf.AlgebraicGeometry.PicardExternalCoefficientsDirectImages)
