# Cyclic higher direct image local vanishing proof imports

## Reason
The proof adds a public comparison module and changes the assigned module's visible
imports and namespace opens. This is required to expose the strictly smaller cyclic
cohomology comparison used by the proof and to import the local-surjectivity API.

## Old
The assigned module imported `Sheaf.Paper.SiteSheafificationSectionsLocal` as a
proof dependency and had a sorry proof.

## New
The assigned module imports
`Sheaf.AlgebraicGeometry.CyclicDerivedHomCohomologyComparison`,
`Mathlib.CategoryTheory.Sites.LocallyBijective`, and
`Mathlib.CategoryTheory.Sites.EpiMono`; it removes
`Sheaf.Paper.SiteSheafificationSectionsLocal`. The public declaration
`AlgebraicGeometry.Etale.exists_cyclicDerivedHom_cohomology_comparison` is added in
the new module.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CyclicHigherDirectImageLocalVanishing | C2 | proof imports and local namespace opens; compiled in this delivery |
| other modules | unclaimed | no recorded downstream users of the new comparison declaration |

## Status
landed 20261013T201739-L-3965810 2026-10-13 (merge of deliver/C2/Sheaf.AlgebraicGeometry.CyclicHigherDirectImageLocalVanishing)
