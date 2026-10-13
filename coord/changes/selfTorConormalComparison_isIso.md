# selfTorConormalComparison_isIso

## Reason
The proof uses `MonoidalCategory` names (`tensorRight`, composition of monoidal
functors) and therefore adds the corresponding namespace opening. This is a proof-level
command change required for the item to elaborate.

## Old
```lean
open CategoryTheory
```

## New
```lean
open CategoryTheory MonoidalCategory
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.SelfTorConormalRegularIso | D3 | required namespace opening for proof |

## Status

landed 20261013T201743-L-3967310 2026-10-13 (merge of deliver/D3/Sheaf.RingTheory.SelfTorConormalRegularIso)
