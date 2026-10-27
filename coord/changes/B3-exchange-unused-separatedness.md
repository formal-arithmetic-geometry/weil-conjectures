# RationalWeilPurity and CommonWeilPurity exchange helpers

## Reason

The item beta_existsUnique assumes only that f₀ is separated; it does not assume
X₀ and Y₀ are separated over the finite field. The auxiliary exchange construction
in RationalWeilPurityNaturalityMate retains unused section assumptions on both
schemes. Its proper/open compactification maps and coefficient realizations need
only the separatedness of f₀. Remove these unused assumptions in the two exchange
namespaces so the existing construction applies to the full auxiliary statement.
The main rational_weil_purity_naturality_mate theorem keeps all its hypotheses.
No target statement, functor formula, comparison map, attribute or public import changes.

## Old

In each of namespaces RationalWeilPurity and CommonWeilPurity:

```lean
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
```

## New

In each of those two namespaces:

```lean
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
```

The affected exchange API consists of
`RationalWeilPurity.rationalExchange_existsUnique`, `rationalExchange`,
`betaComponent`, `beta_naturality`, `beta`, and
`CommonWeilPurity.betaComponent`, `beta_naturality`, `beta`.
Every declaration body is unchanged. Lean drops the unused separatedness binders
from the auxiliary theorem and definition signatures; no argument is added.
The declarations in section Main, including the statement attached to the owning
DAG node, stay verbatim. The helper theorems retain their existing named holes;
this delivery does not count their generalization as a closed hole.

## Users

The downstream.py scan found one existing direct and transitive importer. A
search found no explicit @RationalWeilPurity or @CommonWeilPurity applications.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Remove unused section assumptions in its two auxiliary namespaces. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed | Existing separated inputs still apply; no edit. Compile against the generalized helpers. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | B3 | Reuse the exchange construction without strengthening the item hypotheses. |
| Sheaf.Paper.FrobeniusCompactRationalNormalization | B3 (new) | Compare the rational constructions at the general separated morphism. |

## Status

landed 20261026T235831-L-1458993 2026-10-26 (merge of deliver/B3/Sheaf.Paper.ConstantPurityFrobeniusSquare)
