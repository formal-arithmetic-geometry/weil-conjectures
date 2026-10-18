# Sheaf.Paper.AdicCompletionReduction proof context

## Reason

The stage-3 preflight classifies new `open` commands conservatively as a module-interface
change. The completed naturality proof uses scalar-extension tensor notation. This record
documents the scoped opens. No existing signature, visibility, definition or public import
changes, and no target statement or its meaning changes.

## Old

```lean
universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme
```

## New

```lean
universe t

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme
```

The scoped opens supply notation inside this module. They introduce no exported notation,
attributes or instances. The private helper theorems have complete proofs and occur only
in proofs of existing declarations.

## Users

`python3 tools/downstream.py Sheaf.Paper.AdicCompletionReduction` reports zero downstream
Lean modules. No consumer adaptation is required; existing signatures are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCompletionReduction | J3 | Scoped proof notation and completed proofs. |

## Status

landed 20261018T071158-L-1670015 2026-10-18 (merge of deliver/J3/Sheaf.Paper.AdicCompletionReduction)
