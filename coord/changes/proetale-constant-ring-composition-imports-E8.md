# ProEtaleConstantRingComposition import pruning

## Reason

Prove `AlgebraicGeometry.Scheme.proEtaleCoefficientInverseImageMap_comp` directly from
its constant-section definition, sheafification and the canonical adjunction mate.
The realization transport and the theorem asserting invertibility of coefficient maps
are unused. Replace the former with its precise statement dependency
`ProEtaleInverseImage` and remove the latter. No existing declaration signature,
definition or visibility changes. No target statement or definition changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
```

Both retained imports supply names used in the theorem statement. All proof tools
come from their imports; no additional proof import is needed.

## Users

The read-only `tools/downstream.py` query lists exactly the following downstream module.
It was compiled unchanged as a sandbox probe against the delivered module and passed
in 3.0 seconds. Its other direct imports supply its dependencies, including its own
explicit `ProEtaleConstantRingMap` import. No adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition | E8 | Same theorem signature; one hole proved; unused public imports pruned. |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence | unclaimed | Compiles unchanged; no statement, definition or proof adaptation. |

## Status

landed 20261018T145058-L-3638738 2026-10-18 (merge of deliver/E8/Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition)
