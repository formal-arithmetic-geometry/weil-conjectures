# Sheaf.Paper.IntegralConstantModelHeartClosure proof interface context

## Reason

The proof replaces the original `sorry` with private coefficient transport
lemmas and a constructed integral coefficient isomorphism.  The static
interface check records the added namespace opens, universes, and section
context as changes visible to importers.  The public theorem statement and
all public imports remain unchanged; no consumer requires an adaptation.

## Old

The module had the unchanged public imports and theorem
`AlgebraicGeometry.ProEtale.isConstantModelConstructible_serre_padicIntegers`
with proof `:= by sorry`.  It had no additional namespace opens, universes,
or section declarations between the module section and that theorem.

## New

The public theorem signature is unchanged.  The proof-only imports now are:

```lean
import Sheaf.Paper.IntegralLfpConstantModelComparison
import Sheaf.Paper.IntegralConstructibleSerre
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Mathlib.Algebra.Field.ULift
```

The module adds private helpers for finite-presentation transport,
constructibility transport, and the explicit `integralCoefficientIso`.
The added `open` commands, universe declarations, and local sections are
proof context and do not alter any public declaration or definition.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralConstantModelHeartClosure | H7 | Proof and private context changed; public interface unchanged. |

## Status

landed 20261019T005304-L-2748626 2026-10-19 (merge of deliver/H7/Sheaf.Paper.IntegralConstantModelHeartClosure)
