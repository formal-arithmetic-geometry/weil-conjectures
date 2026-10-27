# Scalar cochain complete-integral import

## Reason

The complete part of `scalar_cochain_averaging_primitives` quantifies over a supplied
continuous linear functional. Currying and composition construct its parameter
family directly. The existence theorem `primeToEll_completeScalar_integral` and
its parameter clause are unused. Replace its public import by its four public
Mathlib prerequisites, retaining the types and instances used in the signatures.
This removes an unnecessary holed module from this import branch. The finite
averaging theorem remains a proof dependency.

## Old

```lean
public import Sheaf.Analysis.PrimeToEllCompleteScalarIntegral
```

## New

```lean
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Category.Profinite.Basic
```

All existing declaration signatures, attributes, visibility and definition bodies
are unchanged. Only the exported existence theorem and its private proof imports
cease to be provided transitively.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.PrimeToEllFiniteQuotientSheafAugmentation | unclaimed | Uses the scalar cochain definitions and theorem, whose signatures are unchanged; does not use the removed existence theorem. Original compiled against this delivery in 26.1 seconds, without warnings or adaptation. |

This is the complete direct-importer list from the current shared source. No other
module references `primeToEll_completeScalar_integral` or imports its module.

## Status

landed 20261026T081418-L-1951781 2026-10-26 (merge of deliver/D4/Sheaf.Analysis.ScalarCochainAveragingPrimitives)
