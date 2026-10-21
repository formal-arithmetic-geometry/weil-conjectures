# Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison

## Reason

Retire the listed duplicate module in `coord/retire-items.tsv`. The complete
`WeilConjectures.AlgebraicGeometry.CartesianChartExchangeComparison` module supplies
the same private `chartRawAdj_pullback` theorem and proof as the Sheaf copy. The
Sheaf duplicate is therefore unnecessary after its three direct consumers migrate
their proof-only imports to the upstream twin.

## Old

The three consumers privately imported the duplicate:

```lean
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison
```

The duplicate module declared the private `chartRawAdj_pullback` theorem.

## New

Each consumer privately imports the adopted source module:

```lean
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeComparison
```

The duplicate is withdrawn through `deleted.txt`. Public imports, declarations,
signatures, target statements and the unit route are unchanged (signatures are rewrapped only).
To pass clean compilation, long consumer lines are wrapped; local proposition-valued proof-body
`letI` bindings become `let`, the unused `hr` hypothesis is explicitly referenced, and the
unused `restrictedOverCoefficient` simp argument at `hz0` is removed. The proof arguments
and their conclusions are preserved. No linter option is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison | B9 | Withdraw duplicate; retain upstream implementation. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftRawNaturality | unclaimed | Migrate proof-only import; declarations and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality | unclaimed | Migrate proof-only import; declarations and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftCoherence | unclaimed | Migrate proof-only import; declarations and proofs unchanged. |

## Status

landed 20261021T002123-L-1488753 2026-10-21 (merge of deliver/B9/Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison)
