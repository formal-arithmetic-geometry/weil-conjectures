# AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_boundary_depths

## Reason

The assigned Sheaf module is listed in `coord/retire-items.tsv` as a duplicate of the adopted
`WeilConjectures` module. The upstream theorem is already proved and has the same boundary-depth
conclusion, with only the unused `hs : s ∉ U` hypothesis omitted. Retire the duplicate and point
the existing DAG Lean attachment at the canonical declaration. No source-library file or target
statement is changed.

## Old

`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths` declared
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_boundary_depths` with the public
binder `(s : S) (hs : s ∉ U)` and otherwise the boundary-depth statement recorded in
`lem-sbc-stalk-normalization-formal-boundary-depths`.

## New

Use the complete declaration
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_boundary_depths` from
`WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths`. Its
signature is identical after removing the unused `hs` binder; its conclusion and proof route are
unchanged. The existing node remains attached to the same mathematical result and records the
canonical module and exact upstream signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths | C5 | Retired duplicate; no surviving Lean importer exists. |
| WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFormalSplit | unclaimed | Already imports and uses the canonical upstream theorem. |

The repository-wide importer scan finds no module importing the withdrawn Sheaf copy. The
upstream FormalSplit consumer remains unchanged.

## Status

landed 20261021T002928-L-1579294 2026-10-21 (merge of deliver/C5/Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths)
