# Sheaf.Paper.PodHomChainCtfDomains import interface

## Reason

The complete proof uses only the canonical restricted functors, adjunctions and
projection already exposed by PodCtfPairingMaps. Remove unused direct imports.
All existing declaration signatures, visibility, definitions and docstrings remain unchanged.

## Old

```lean
public import Sheaf.Paper.PodCtfPairingMaps
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.FiniteTorStability
import Sheaf.Paper.SfIntegralDirectImageConstructible
```

## New

```lean
public import Sheaf.Paper.PodCtfPairingMaps
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.VerdierHomChainComposition | unclaimed in local claim snapshot | Only downstream module reported by tools/downstream.py; imports the item privately and already imports Etale.Derived.Adjunctions itself. No adaptation. |

DerivedPullbackTensorHom and ExchangeProjectionSuppliedDomains remain publicly
reexported through PodCtfPairingMaps. The removed upstream Adjunctions import
contributes no declaration used by the item; its sole downstream user has an
explicit private import of that module. Neither the existing signatures nor any
operation data changes, so target meaning is unchanged. No consumer is edited.

## Status

landed 20261025T123259-L-1852327 2026-10-25 (merge of deliver/M1/Sheaf.Paper.PodHomChainCtfDomains)
