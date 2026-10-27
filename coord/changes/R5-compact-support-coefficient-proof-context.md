# Compact-support coefficient-model proof context

## Reason

The parent proof checked but exceeded the single-file compilation limit. The initial
proof context now respects transparency, so its marked irreducible definitions need
not unfold during unification. Two private arithmetic imports are replaced by public
basis APIs and proved local helpers. The existing normalized comparison specification
lemmas remain in use; unfolding their chosen-comparison definitions was expensive.

No existing declaration signature, definition body, public import, global attribute,
or target meaning changes. No consumer adaptation is required.

## Old

The initial proof context and arithmetic imports were:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
import all Sheaf.Paper.CompletedIntegralFiniteFree
import all Sheaf.CategoryTheory.AdicBasisLimit
```

All existing public signatures and definitions are retained verbatim.

## New

The initial proof context and replacement arithmetic imports are:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
import Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Quotient
```

The private helpers `coefficientIntegralBasis` and `coefficientQuotientBasis` prove the
same coordinate constructions using these public APIs. The theorem combining the
ordinary component isomorphisms also uses a proved private tensor-naturality helper.
The existing private import of `FiniteFreeCompletedScalarComparison` is retained.
The naturality proof uses explicit equality transitivity; the quotient square
applies the functor composition law directly. These replace generic rewrites that
cannot match the restricted coefficient aliases at the implicit transparency level.
The options affect only this module's elaboration, not importing modules.

## Users

There are no changed public names to propagate to downstream consumers. The only
module whose elaboration context changes is the item itself. No other existing
module is adapted, and no declaration is removed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportCoefficientModels | R5 | Proof context and private helpers only. |

## Status

landed 20261026T070817-L-3660453 2026-10-26 (merge of deliver/R5/Sheaf.Paper.CompactSupportCoefficientModels)
