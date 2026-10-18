# AlgebraicGeometry.exists_finiteDimensional_top_coherent_cohomology_quotient

## Reason
The target proof is decomposed through the geometric projective-closure output: a
finite-dimensional quotient map together with the proper surjective Chow modification.
The target module also drops proof-only imports from the abandoned induction route.

## Old
No declaration existed on `sheaf-dag`.

## New
`AlgebraicGeometry.exists_finiteDimensional_top_coherent_cohomology_quotient` in
`Sheaf.AlgebraicGeometry.TopCoherentCohomologyFiniteQuotient`.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.TopCoherentCohomologyFinite` | R1 | imports the split for its proof and applies `FiniteDimensional.of_surjective` |

## Status
landed 20261018T071216-L-1675499 2026-10-18 (merge of deliver/R1/Sheaf.AlgebraicGeometry.TopCoherentCohomologyFinite)
