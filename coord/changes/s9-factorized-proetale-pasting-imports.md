# proEtaleFactorizedPullback_pasting

## Reason

Both original proof holes are closed. The published coherence and ordinary-normalization
interface already incorporates the canonical coefficient-map and pullback-composition
facts. Their redundant public imports are removed. Exact localization gives the
representative formulas for all complexes, so the proof-only K-flat-preservation import
is also unnecessary. No existing statement or definition changes.

The module adds proved private categorical helpers, local irreducibility attributes for
large construction terms, and local instances for preservation by composite functors.
The generic helpers live in closed sections with their own variables. None of these
commands introduces public data, notation, or instances. Their purpose is to check the
same canonical comparisons efficiently; the complete module compiles in 5.6 seconds.

## Old

```lean
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.Paper.KFlatRingedToposPullback
```

## New

The four imports above are removed. All remaining original public imports are retained.
Every existing declaration signature and every existing definition body is verbatim.
The only existing theorem bodies changed are the two originally containing `sorry`.
No target statement or definition used by a target changes its meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting | S9 | Both proof holes closed; redundant imports removed; existing signatures and definitions preserved. |

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting --uses proEtaleFactorizedPullback_pasting`
returned no downstream users in the current shared repository. A direct search of
`lean/` found no importing module and no external declaration references. Thus no
consumer adaptation is needed. Unfinished DAG parents continue to use the same public
declarations when their proofs are implemented. The item's node and its statement
dependencies are retained; only its proof route and obsolete tool approvals are pruned.
No module is withdrawn.

## Status

landed 20261021T161413-L-4165304 2026-10-21 (merge of deliver/S9/Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting)
