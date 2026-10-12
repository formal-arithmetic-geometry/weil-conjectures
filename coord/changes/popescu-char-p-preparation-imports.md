# Popescu preparation imports
## Reason
The composition proof uses two private intermediate imports; three unused public imports
are removed. This does not change the main theorem's signature or the downstream caller.
## Old
```lean
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
```
## New
All three public-import lines above are removed (replacement: no lines).
All remaining public imports retain their existing visibility.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.PopescuCharPPreparation | V3 | three unused public imports removed |
| Sheaf.RingTheory.PopescuResolveCharP | unclaimed in checkout | original source compiles unchanged against sandbox delivery |
## Status
landed 20261012T150958-L-2232705 2026-10-12 (merge of deliver/V3/Sheaf.RingTheory.PopescuCharPPreparation)
