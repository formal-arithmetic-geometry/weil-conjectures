# Sheaf.Paper.RingedKunnethFactorizations public imports

## Reason

The proof uses the specified square comparison and its conjugate directly. The independent
pushforward-composition existence theorem is unnecessary, and the tensor-pullback API already
arrives through RingedExchangeTensorCoherence. Remove their redundant public imports together
with the unused proof import of RingedComparisonTensorAdjunction. No public construction,
statement, universe, instance or declaration visibility changes.

## Old

```lean
public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.RingedComparisonTensorAdjunction
```

## New

```lean
public import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedSquareTensorCompatibility
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedKunnethFactorizations | R8 | Own module compiles; definitions and statement unchanged. |

No module in lean/Sheaf or lean/WeilConjectures imports this module or uses its theorem in
this snapshot (checked by rg over both roots and tools/downstream.py with --uses). Thus no
consumer needs adaptation, and no
target statement changes meaning. The two new imports are proof-only.

## Status

landed 20261019T005416-L-2765672 2026-10-19 (merge of deliver/R8/Sheaf.Paper.RingedKunnethFactorizations)
