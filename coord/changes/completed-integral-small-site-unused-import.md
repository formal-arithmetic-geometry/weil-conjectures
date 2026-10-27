# Sheaf.Paper.CompletedIntegralOnSmallSite public imports

## Reason

Remove the unused coefficient-universe transport import noted by the stage-2 reviewer.
The construction and both completed proofs use the retained completed-integral import
and its public Mathlib dependencies. No declaration signature or definition body changes.

## Old

```lean
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.CochainCoefficientUniverseTransport
```

## New

```lean
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
```

## Users

`tools/downstream.py Sheaf.Paper.CompletedIntegralOnSmallSite` lists the following
two modules. Neither names `SheafOfModules.CochainUniverseTransport` or any declaration
from the removed module. Their explicit imports already provide the module, tensor and
ring sheaf infrastructure they use. No consumer adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedLisseUniverseTransport | unchanged; no adaptation | Uses the same CompletedSite declarations and explicitly imports RingedSiteModules and CochainTensorUniverses. |
| Sheaf.Paper.IntegralLocalModelFiniteMatrixReduction | unchanged; no adaptation | Uses the same CompletedSite declarations and explicitly imports RingedSiteModules and CochainTensorUniverses. |

## Status

landed 20261025T161818-L-117560 2026-10-25 (merge of deliver/A7/Sheaf.Paper.CompletedIntegralOnSmallSite)
