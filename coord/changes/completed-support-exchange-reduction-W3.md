# AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.twoSubstitutions

## Reason

The second successive substitution needs the strict reduction square for one exchange,
before applying Rlim. The existing exchangeSubstitution theorem gives an equation after
Rlim; it does not supply this stricter square. Isolate that subcalculation in a new module.
To make it available to the original module without an import cycle, relocate the existing
ambient definitions and assertions (the prefix ending at exchangeSubstitution) verbatim to
CompletedSupportIntermediateTowerCore. This is a dependency refactor, not a response to a
compile-time limit. No declaration signature or definition body changes.

## Old

The original module contains all ambient and finite declarations directly. Its original
successive-substitution proof is exactly:

```lean
  sorry
```

The prefix starts with these verbatim declarations:

```lean
abbrev openExtension {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j] :=
  (moduleJ A j).mapDerivedCategory

def openAdjunction {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j] :
    openExtension (A := A) j ⊣ pull (A := A) j :=
  ((moduleJAdj A j).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
    (modulePullback A j).rightDerivedFunctorIsoMapDerivedCategory
```

## New

Every relocated declaration keeps its original namespace, full type, visibility and body.
The original module exports it through:

```lean
public import Sheaf.Paper.CompletedSupportIntermediateTowerCore
import Sheaf.Paper.CompletedSupportExchangeReduction
```

The latter import supplies only a proof dependency. The new theorem
completedExchange_reduction states a single exchange's strict reduction square, with a
source, full proof in words and its own DAG node. twoSubstitutions now proves its first
clause by exchangeSubstitution and naturality, its second by naturality of mu followed by
the new reduced square under the two functors, and its third by associativity and map_comp.
The ambient comparisons receive their own node, and the original node retains the finite,
origin and successive-substitution assertions. No moved hole counts as closed or added.

## Users

The read-only command `tools/downstream.py Sheaf.Paper.CompletedSupportIntermediateTower
--uses twoSubstitutions` reports zero downstream Lean modules and only the original module
as a textual user of twoSubstitutions. The DAG parents retain their existing import and
attachment to the original module; no assertion or target meaning changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedSupportIntermediateTower | W3 | Same exported API; one hole decomposed |
| Sheaf.Paper.CompletedSupportIntermediateTowerCore | W3, new | Original ambient prefix relocated |
| Sheaf.Paper.CompletedSupportExchangeReduction | W3, new | One strict reduction square obligation |

## Status

landed 20261026T024204-L-645451 2026-10-26 (merge of deliver/W3/Sheaf.Paper.CompletedSupportIntermediateTower)
