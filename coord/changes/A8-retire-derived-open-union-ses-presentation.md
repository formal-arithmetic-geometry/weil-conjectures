# AlgebraicGeometry.derived_open_union_ses_presentation

## Reason

The assigned module is a human-authorized `retire` item in
`coord/retire-items.tsv`. The adopted upstream twin
`WeilConjectures.AlgebraicGeometry.DerivedOpenUnionSESPresentation` already
provides the same public theorem and is the implementation used by the live
upstream consumer. The Sheaf copy has no current Lean importers and is a
redundant duplicate dependency path. Withdraw the Sheaf module and redirect
its DAG attachment to the upstream declaration. No source-library file or
target statement changes.

## Old

The withdrawn module `Sheaf.AlgebraicGeometry.DerivedOpenUnionSESPresentation`
publicly declared
`AlgebraicGeometry.derived_open_union_ses_presentation` with the theorem
statement recorded in node `lem-sc-derived-open-union-ses-presentation`:
for a scheme `X`, derived categories on `X` and its open localizations,
opens `U,V`, supplied right adjoints `G` and adjunctions `adj`, and an object
`E`, it constructs a short exact complex presentation of the union, biproduct,
and overlap direct-image terms, together with the displayed first-arrow
comparison. The Sheaf file had zero `sorry` declarations.

## New

The Sheaf module is withdrawn through `deleted.txt`; the delivery tool writes
an empty module stub. The DAG node now points to the existing upstream
`WeilConjectures.AlgebraicGeometry.DerivedOpenUnionSESPresentation` and its
unchanged `AlgebraicGeometry.derived_open_union_ses_presentation` declaration.
The upstream theorem has the same statement and proof content; only its
imports use the upstream dependency namespace. All node statement, proof,
unit, source, and review fields remain unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedOpenUnionSESPresentation | A8 | Withdraw the duplicate module; its DAG attachment is redirected upstream. |
| WeilConjectures.AlgebraicGeometry.DerivedOpenUnionAdjunctionTriangle | upstream source | Already imports and uses the upstream twin; unchanged. |

A fresh scan of both Lean roots found no importer of the Sheaf module and no
other declaration use requiring adaptation. No target statement or definition
changes, and no upstream source module is edited.

## Status

landed 20261021T002117-L-1486836 2026-10-21 (merge of deliver/A8/Sheaf.AlgebraicGeometry.DerivedOpenUnionSESPresentation)
