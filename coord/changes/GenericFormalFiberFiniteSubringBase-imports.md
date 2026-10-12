# GenericFormalFiberFiniteSubringBase imports

## Reason

The second reader found an unused fraction-ring import and a publicly exported
proof dependency. The statement only needs GRing and its public dependencies.
No declaration signature or definition changes.

## Old

```lean
public import Sheaf.RingTheory.FormalFibreQuasiFiniteAscent
public import Mathlib.RingTheory.Localization.FractionRing
```

## New

```lean
public import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.FormalFibreQuasiFiniteAscent
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.FiniteSubringGenericFormalFiber | unclaimed | Sole direct importer; imports GRing, FractionRing, and FormalFibreQuasiFiniteAscent itself. Original compiled against the changed module. No adaptation or mathematical change. |

There are no changed declarations, so no target's meaning changes. The original
direct importer supplies the removed exports itself; its public interface is
unchanged, and consequently downstream users retain those imports.

## Status

landed 20261012T150950-L-2229739 2026-10-12 (merge of deliver/D2/Sheaf.RingTheory.GenericFormalFiberFiniteSubringBase)
