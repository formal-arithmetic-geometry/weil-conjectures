# AlgebraicGeometry.Scheme.Modules.finite_H_of_shortExact_middle

## Reason

The Sheaf declaration duplicates the upstream declaration
`AlgebraicGeometry.Scheme.Modules.finite_H_of_shortExact_extension`. The Sheaf module has
no importers, while the upstream module is already available to the source library. Remove
the duplicate module and repoint its DAG node to the upstream declaration.

## Old

`Sheaf.AlgebraicGeometry.CohomologyFiniteExtension` publicly declared
`AlgebraicGeometry.Scheme.Modules.finite_H_of_shortExact_middle` and publicly imported
`WeilConjectures.AlgebraicGeometry.Cohomology.Defs`.

## New

`Sheaf.AlgebraicGeometry.CohomologyFiniteExtension` is withdrawn. The DAG node uses
`WeilConjectures.AlgebraicGeometry.CohomologyFiniteExtension`, declaration
`AlgebraicGeometry.Scheme.Modules.finite_H_of_shortExact_extension`, with the identical
statement and proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| none | none | no Lean importers; withdrawal is safe |

## Status

landed 20261020T221208-L-4155778 2026-10-20 (merge of deliver/H2/Sheaf.AlgebraicGeometry.CohomologyFiniteExtension)
