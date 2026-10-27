# Sheaf.Paper.NormalizedVectorPurityScalarCompatibility and scalar core

## Reason

The fixed-witness compatibility proof uses a new strictly smaller public theorem
`scalar_source_compatibility_core` in a dedicated module. The item module imports that
module privately for its proof; the existing target theorem signature is unchanged.

## Old

`Sheaf.Paper.NormalizedVectorPurityScalarCompatibility` contained the fixed-witness theorem
with a `sorry` proof and imported only `Sheaf.Paper.VectorPurityFiniteReduction`.

## New

The item theorem has a complete proof and privately imports
`Sheaf.Paper.NormalizedVectorPurityScalarCore`. The new module publicly declares
`WeilConjectures.PurityFiniteSetting.scalar_source_compatibility_core`, whose statement is a
strict subset of the item conclusion: source-map invertibility and the normalized mate equation.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.NormalizedVectorPurityScalarReduction | unclaimed/parent | Its existing import of the item sees the same theorem signature; no adaptation. |
| Sheaf.Paper.NormalizedVectorPurityScalarCompatibility | T1 | Uses the new core declaration in its proof. |

## Status

landed 20261027T210232-L-1677227 2026-10-27 (merge of deliver/T1/Sheaf.Paper.NormalizedVectorPurityScalarCompatibility)
