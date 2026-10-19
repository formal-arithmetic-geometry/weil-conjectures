# WeilConjectures.brownHypothesesGeneration

## Reason

The generic private compactness and localizing-closure comparison lemmas use two independent
universes for their object and morphism types. The source command therefore adds universe
names `v` and `w`. The delivery preflight classifies a changed universe command as an interface
change requiring this record. The existing public theorem still uses only `u`, and its
signature is textually identical to the original. No existing definition changes.

## Old

```lean
universe u
```

## New

```lean
universe u v w
```

The additional names occur in private helper declarations. All original public imports and
all binders, universes, and conclusions of `WeilConjectures.brownHypothesesGeneration` remain
identical. The proved public coefficient-transport helper is in its own new module.

## Users

`python3 tools/downstream.py Sheaf.Paper.BrownHypothesesGeneration --uses
WeilConjectures.brownHypothesesGeneration` lists 209 transitive downstream modules, but its
only textual use of the theorem name is the declaration in the item itself. Universe names
are local elaboration parameters, not exported constants; downstream module declarations
cannot refer to these local parameters. Thus every downstream statement retains its meaning
and no consumer adaptation is needed. No target statement or definition changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Add universe names for private helpers; existing public theorem signature identical. |

## Status

landed 20261019T034256-L-416395 2026-10-19 (merge of deliver/E1/Sheaf.Paper.BrownHypothesesGeneration)
