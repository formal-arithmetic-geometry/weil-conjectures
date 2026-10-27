# AlgebraicGeometry.Scheme.Modules.isAmple_tensorPullback_tensorPow_of_relative

## Reason

The complete proof uses monoidal notation, opposite-open notation, scalar extension
notation, and backward elaboration for the existing module/sheaf coercions. Preflight
classifies these added file commands as a visible change and requests this record.
They only configure elaboration of this file. No public declaration signature,
attribute, definition, instance, or public import changes. The theorem proof is complete;
all new declarations are private. The returned-head repair removes the redundant private
`tensorPullback_invertible` and adds a proof-only import of BertiniIncidenceNaturality
to use the existing generic `AlgebraicGeometry.bertiniTensorPullback_invertible` directly
at all five call sites. This adds no public declaration, instance, or public import.

## Old

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
```

## New

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped ChangeOfRings
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.RelativeAmpleAbsoluteTwist
--uses isAmple_tensorPullback_tensorPow_of_relative` lists the following consumer
and the defining module itself. The existing theorem signature and all public imports
are unchanged. The consumer's application has identical arguments and conclusion and
requires no adaptation; the new file options and open commands do not propagate through
imports. No target statement or definition used in a target changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CompositionFiniteAffineTwistBounds | unclaimed | No interface change or adaptation. |
| Sheaf.AlgebraicGeometry.RelativeAmpleAbsoluteTwist | X2 | New private proof helpers and completed theorem proof. |

## Status

landed 20261023T152128-L-452864 2026-10-23 (merge of deliver/X2/Sheaf.AlgebraicGeometry.RelativeAmpleAbsoluteTwist)
