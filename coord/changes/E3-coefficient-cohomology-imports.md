# DerivedCategory.coefficientCohomologyModules (import pruning)

## Reason

The positive-level finite-ring theorem is not used by any definition or proof here.
The coefficient rings and integral ideal remain available from the existing public
import of Sheaf.Paper.FiniteFieldFiber, which publicly imports CoefficientExtension.
Tensor-product finiteness is used only to prove coefficientQbarCohomology_finite.

## Old

```lean
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.RingTheory.TensorProduct.Finite
```

## New

```lean
import Mathlib.RingTheory.TensorProduct.Finite
```

The first import is removed; the second becomes proof-only. Every existing declaration,
statement, definition, visibility, and algebraic-closure hypothesis is preserved.

## Users

`python3 tools/downstream.py Sheaf.Paper.CoefficientCohomologyModules` reports zero
modules downstream. No consumer needs adaptation, and no target statement uses a
changed definition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientCohomologyModules | E3 | Six proofs filled; imports pruned as above. |

## Status

landed 20261018T141024-L-3141326 2026-10-18 (merge of deliver/E3/Sheaf.Paper.CoefficientCohomologyModules)
