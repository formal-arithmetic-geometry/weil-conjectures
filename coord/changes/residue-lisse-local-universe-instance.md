# residueLisseAbLocallyBijective local instance

## Reason

The independent-universe reconstruction and slice functors require the exact
AddCommGrpCat universe t+1. The existing essentially-small-site instance is pinned
locally during this module's proofs. Preflight classifies the new local attribute
command as a visibility change and requires this record. It is a local attribute
on a new private proved theorem; no existing public signature or definition changes.

## Old

No local attribute command or private helper existed in the shared source.

## New

```lean
private theorem residueLisseAbLocallyBijective (X : Scheme.{t}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  finitePerfectModelsAbLocallyBijective X
attribute [local instance] residueLisseAbLocallyBijective
```

## Users

`tools/downstream.py Sheaf.Paper.ResidueLissePerfectLift --uses
residueLisseAbLocallyBijective` reports 1334 transitive importers and zero users
of this new private name. The attribute is local to this module, so all importers
retain their public signatures, definitions and instance behavior.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ResidueLissePerfectLift | D7 | private proof elaboration only |

## Status

landed 20261019T192711-L-1856737 2026-10-19 (merge of deliver/D7/Sheaf.Paper.ResidueLissePerfectLift)
