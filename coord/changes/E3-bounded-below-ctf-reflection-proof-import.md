# BoundedBelowCtfReflection proof imports

## Reason

The completed proof uses the new constructibility-reflection helper and the
characteristic-cardinality API. These are proof-only dependencies; the target
statement and all existing declaration signatures remain unchanged. The
linter option suppresses style diagnostics that the delivery checker treats as
errors.

## Old

`Sheaf.Paper.BoundedBelowCtfReflection` ended its private imports after
`Sheaf.Paper.ComparisonTorAmplitude` and contained no linter option.

## New

The private imports now also include:

```lean
import Sheaf.Paper.BoundedBelowConstructibleReflection
import Mathlib.Algebra.CharP.CharAndCard
```

The module sets `linter.style.haveILetI` to false while retaining the existing
public imports and theorem signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BoundedBelowCtfReflection | E3 | Proof-only imports and linter option; theorem signature unchanged. |

No other module is adapted.

## Status

landed 20261020T221130-L-4147768 2026-10-20 (merge of deliver/E3/Sheaf.Paper.BoundedBelowCtfReflection)
