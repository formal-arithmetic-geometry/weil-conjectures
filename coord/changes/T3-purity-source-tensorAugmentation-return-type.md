# WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation

## Reason

The item repeatedly exceeded the 60-second single-file limit after type errors
were repaired. Profiling identified repeated type checking of the large
uniqueness specifications. Give this selected-witness definition its existing
return type explicitly, so later applications do not infer that type through the
uniqueness theorem. Its term, visibility and public attributes are unchanged.
Local irreducibility and canonical instance priorities apply only within this
module. They do not change any downstream reduction behavior or mathematical
meaning. No target statement or definition meaning changes.

## Old

```lean
def tensorAugmentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :=
  (tensorAugmentation_existsUnique l E T).exists.choose
```

## New

```lean
def tensorAugmentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    ordinaryTotal l E T ⟶ integralOperationsTensorComplexFunctor l E T :=
  (tensorAugmentation_existsUnique l E T).exists.choose
```

## Users

The following are the declaration users reported by `tools/downstream.py --uses`.
All transitive importers retain the identical public constant and body. No
consumer source adaptation is required: the annotation records the already
inferred type.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.PuritySourceTransports` | T3 | Same elaborated type and body; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed | Same elaborated type and body; no adaptation. |

## Status

landed 20261025T164341-L-1002274 2026-10-25 (merge of deliver/T3/Sheaf.Paper.PuritySourceTransports)
