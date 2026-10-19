# AlgebraicGeometry.ProEtale.finiteScalarUnitComparison

## Reason

Remove the unused public realization import while proving the finite noncommutative
scalar-unit comparison. No declaration signature, definition, or instance changes.
The new proved underlying-comparison theorem has its own module and node.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
```

## New

The unused public import is removed. The proof privately imports
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction`,
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleUnderlying`, and
`Mathlib.CategoryTheory.Adjunction.Mates`.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleFiniteScalarUnitComparison
--uses finiteScalarUnitComparison` now reports 123 downstream modules, but the theorem
name occurs only in its own module. The direct importer is
`Sheaf.AlgebraicGeometry.ProEtaleSupportedKernelComplex`; its own public import of
`ProEtaleFiniteModuleAdjunction` already supplies `SfIntrinsicRealizationTransport`.
The removed public import therefore removes no declaration available to this consumer.
The existing theorem and definition signatures are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleFiniteScalarUnitComparison | J3 | Proof completed; unused public import removed; existing signatures identical. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedKernelComplex | unchanged | Direct importer; already publicly imports the removed realization dependency through ProEtaleFiniteModuleAdjunction. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleUnderlying | new, J3 | Adds a proved unit-normalized abelian comparison; no existing interface changes. |

No target definition or statement changes. No consumer adaptations are needed.

## Status

landed 20261019T005305-L-2749043 2026-10-19 (merge of deliver/J3/Sheaf.AlgebraicGeometry.ProEtaleFiniteScalarUnitComparison)
