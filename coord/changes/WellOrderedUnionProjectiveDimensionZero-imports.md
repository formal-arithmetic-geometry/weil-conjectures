# Sheaf.RingTheory.WellOrderedUnionProjectiveDimensionZero imports

## Reason

The proof does not use declarations supplied specifically by the two additional
public imports. `Sheaf.RingTheory.GlobalDimension` already supplies all needed
interfaces, so these imports are proof-local redundancies and are removed to
keep the module interface minimal.

## Old

```lean
public import Sheaf.RingTheory.GlobalDimension
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs
```

## New

```lean
public import Sheaf.RingTheory.GlobalDimension
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.WellOrderedUnionProjectiveDimension | unclaimed | recompiles against the reduced public interface; its direct use is only of the target theorem |

## Status

landed 20261013T011936-L-2766236 2026-10-13 (merge of deliver/T1/Sheaf.RingTheory.WellOrderedUnionProjectiveDimensionZero)
