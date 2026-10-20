# AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_affine_local_cohomology

## Reason

Restore the quarantined item listed in `coord/rework.tsv`. The old public import
now names an empty withdrawn module, so the public theorem cannot elaborate
`X.Modules` (and, after importing only that notation, `F.IsQuasicoherent`). The
field-linear operations have moved to the adopted source library. Import their
actual module publicly because they occur in the theorem's statement.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The original full file is preserved at
`quarantine/Sheaf/AlgebraicGeometry/PicardExternalCoefficientsAffineLocalCohomology.lean`.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

Restore the item at its original Lean path with this single replacement. All
declaration signatures, proof bodies, attributes and remaining imports are
identical to the quarantine source. No definition or target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineLocalCohomology | E2 | Restored; compiles cleanly after replacing the stale public import. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsDirectImages | unclaimed, quarantined | Preserves the theorem used in its proof at the same name and signature. No edit needed for this import repair. |

`tools/downstream.py` reports the item as unknown because it is quarantined.
An `rg` search of both `lean/` and `quarantine/` finds no active Lean consumer
and only the quarantined direct-image module above. DAG parents and the item's
Lean attachment and proof dependencies remain intact. No consumer statement
changes and no forced adaptation is included.

## Status

landed 20261020T152956-L-2857686 2026-10-20 (merge of deliver/E2/Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineLocalCohomology)
