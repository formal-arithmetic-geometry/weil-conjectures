# Sheaf.AlgebraicGeometry.CompositeFibreLocalModels imports and fibre stalk API

## Reason

The proof removes an unused public import and adds a public fibre-stalk API used by the
composite-fibre theorem. The declarations express the existing scheme-fibre construction and
are needed by downstream fibre-dimension arguments.

## Old

`public import Sheaf.Topology.PresheafModuleStalkFunctor` in
`Sheaf.AlgebraicGeometry.CompositeFibreLocalModels`; the module had no fibre-stalk map API.

## New

The unused public import is removed. The new module
`Sheaf.AlgebraicGeometry.FibreStalkQuotient` exports
`AlgebraicGeometry.Scheme.Hom.fiberStalkMap` and
`AlgebraicGeometry.Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv`.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint` | unclaimed | imports the composite-fibre module; it continues to compile and can use the new fibre-stalk API |

## Status

landed 20261018T062722-L-639581 2026-10-18 (merge of deliver/D3/Sheaf.AlgebraicGeometry.CompositeFibreLocalModels)
