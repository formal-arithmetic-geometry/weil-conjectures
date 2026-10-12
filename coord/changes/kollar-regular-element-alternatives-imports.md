# IsLocalRing.kollar_regular_element_alternatives imports

## Reason
The statement needs IsSMulRegular and QuotSMulTop, provided by the smaller regular-element
module. It does not need regular sequences. Proof dependencies use plain imports.
No declaration statement or definition changes.

## Old
```lean
public import Mathlib.RingTheory.Regular.RegularSequence
```

## New
```lean
public import Mathlib.RingTheory.Regular.IsSMulRegular
```

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.KollarLocalDichotomy | none | Direct importer; independently publicly imports Sheaf.RingTheory.Depth, which publicly imports RegularSequence, so all its regular-sequence declarations remain available and its statements are unchanged. Compiled unchanged against the delivered module. |

All farther imports pass through KollarLocalDichotomy, whose public Depth import independently exposes
RegularSequence. Their available declarations and target definitions are unchanged.

## Status
landed 20261012T135220-L-1656735 2026-10-12 (merge of deliver/B3/Sheaf.RingTheory.KollarRegularElementAlternatives)
