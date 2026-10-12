# PopescuSmoothLiftModuloEightAux proof import

## Reason

The second-reader brief requires imports used only by proofs to be plain
imports. PopescuLifting supplies the theorem applied in the proof, but nothing
in the existing public signature needs that module. Privatizing its import
changes import visibility, so the preflight requires this record.

## Old

```lean
public import Sheaf.RingTheory.PopescuLifting
```

## New

```lean
import Sheaf.RingTheory.PopescuLifting
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.PopescuSmoothLiftModuloEight | unclaimed | None: it already imports PopescuLifting directly, and imports this auxiliary module only privately. Its signatures and proof are unchanged. |

Ran tools/downstream.py Sheaf.RingTheory.PopescuSmoothLiftModuloEightAux
--uses Algebra.popescu_lifting: zero downstream declaration users. The raw
transitive graph contains 188 modules, but the sole direct importer above
already imports PopescuLifting and forms a private import boundary. Thus this
visibility change cannot affect their available declarations. No target
statement or definition changes its meaning. No forced adaptation is needed.

## Status

landed 20261012T173912-L-3308201 2026-10-12 (merge of deliver/U2/Sheaf.RingTheory.PopescuSmoothLiftModuloEightAux)
