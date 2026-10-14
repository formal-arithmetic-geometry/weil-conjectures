# picard residue proof imports

## Reason

The proof requires the existing structure-sheaf cohomology functoriality theorem,
Mathlib pullback pasting/isomorphism lemmas, tensor-pullback adjunction uniqueness,
and the invertibility bridge. These are proof-only imports and do not alter any
public declaration or statement.

## Old

The item imported the derived fibre, tensor pullback, structure-sheaf cohomology,
derived direct image, invertible modules, morphism properties, and its original
proof imports.

## New

The same imports remain, with proof-only imports for
`Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackFunctorial`,
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting`,
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso`,
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, and
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceFibreComparison | N1 | proof imports only |

## Status

landed 20261014T013039-L-3414892 2026-10-14 (merge of deliver/N1/Sheaf.AlgebraicGeometry.PicardResidueHomologySourceFibreComparison)
