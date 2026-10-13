# pullback tensor unit proof attributes

## Reason

The proof needs local monoidal instances and an explicit `open` scope for presheaf and scheme section notation. These commands are scoped locally and do not alter any public declaration or exported interface.

## Old

The module had only `open CategoryTheory MonoidalCategory` and no local instance registrations.

## New

The module adds `open Opposite TopologicalSpace` and local attributes for the existing monoidal instances used by the private proof helpers.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PullbackTensorUnitSection | Q4 | proof elaboration only; target signature unchanged |

## Status

landed 20261013T132737-L-4152292 2026-10-13 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.PullbackTensorUnitSection)
