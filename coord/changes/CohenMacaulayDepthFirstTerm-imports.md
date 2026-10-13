# IsLocalRing.first_term_depth_ge imports

## Reason

The statement uses ModuleCat and its basic category structures. The stronger
ModuleCat.Abelian public import is unnecessary; ModuleCat.Basic suffices. The proof
compiles with the smaller import and its existing private proof dependencies.
No declaration signature or definition changes, and no target meaning changes.

## Old

```lean
public import Mathlib.Algebra.Category.ModuleCat.Abelian
```

## New

```lean
public import Mathlib.Algebra.Category.ModuleCat.Basic
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.CohenMacaulayFreeResolutionMCM | unclaimed | Unchanged; compiled against the delivery in a scratch overlay. It directly publicly imports ModuleCat.Abelian itself. |

This is the only direct importer. It preserves its own public Abelian import,
so modules further downstream retain that interface. No forced adaptations.

## Status

landed 20261013T010617-L-2671622 2026-10-13 (merge of deliver/M1/Sheaf.RingTheory.CohenMacaulayDepthFirstTerm)
