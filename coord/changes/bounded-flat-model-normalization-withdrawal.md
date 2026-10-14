# Withdrawal of the obsolete bounded-flat normalization theorem

## Reason

The replacement shift-saturated/perfect-generation route makes the theorem
`exists_bounded_flat_model_normalization` unreachable. The module carrying that
theorem is therefore withdrawn. Its bounded-flat predicate is still part of the
interfaces of four already landed, held modules, so that predicate is retained
in a replacement module and those modules receive only the forced import edit.
Their declarations, visibility, statements, and proof bodies are preserved.

## Old

`Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization` contained
`AlgebraicGeometry.boundedFlatShiftRepresentative` and the theorem
`AlgebraicGeometry.exists_bounded_flat_model_normalization`.
The four downstream modules publicly imported it:

- `Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationIsIso`
- `Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationUnshiftedIsIso`
- `Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso`
- `Sheaf.AlgebraicGeometry.FlatTelescopeSumModels`

## New

`BoundedFlatModelNormalization.lean` is withdrawn as the empty withdrawal module delivered here.
The unchanged predicate declaration is moved to
`Sheaf.AlgebraicGeometry.BoundedFlatShiftRepresentative` and its DAG attachment
is updated to that module. Each downstream module changes exactly one public
import line, replacing `BoundedFlatModelNormalization` with
`BoundedFlatShiftRepresentative`; all existing declarations and visibility stay
identical. The retired normalization theorem remains detached from Lean in its
DAG node.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationIsIso | G2 | One forced public import replacement; theorem and visibility preserved. |
| Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationUnshiftedIsIso | G2 | One forced public import replacement; theorem and visibility preserved. |
| Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso | E1 | One forced public import replacement; theorem and visibility preserved. |
| Sheaf.AlgebraicGeometry.FlatTelescopeSumModels | Y3 | One forced public import replacement; theorem and visibility preserved. |

## Status

landed 20261014T174623-L-3170348 2026-10-14 (merge of deliver/F2/Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization)
