# AlgebraicGeometry.ProEtale.cartesianCoefficients_finiteFree proof context

## Reason

Complete the finite-free coefficient proof using private proved coordinate, localization,
transport, compatibility and finite-limit helpers. Local elaboration options and instance
attributes prevent repeated inference through the explicit sheaf tensor and pullback
constructions. No existing declaration signature, definition body, public import or target
statement changes. All additional imports are private.

## Old

The item had its existing coefficient definitions and one theorem with body `by sorry`.
There were no corresponding private helpers or added local proof-context commands.

## New

The existing theorem has the same signature and a complete proof. The added commands are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] upperStarFromPoint Mod.extendScalars
```

The two transparency options affect elaboration only. The attributes are local to the
module and are not exported. The generic transport proof introduces Mathlib's proved finite-to-binary biproduct
conversion only as local proposition-valued hypotheses. The irreducibility command retains the actual source constructions and their
proved APIs; no opaque declaration or replacement object is introduced. Each new private
helper has a complete proof. No private declaration occurs in a public signature or in
the body of an existing public data definition.

## Users

`tools/downstream.py Sheaf.Paper.CartesianCoefficientsFiniteFree --uses
cartesianCoefficients_finiteFree` found the item and three direct declaration consumers.
All retain the identical theorem type and coefficient definitions. The 234 transitive
importers also see the same public imports and instance environment. No consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | B9 | One theorem proved; private helpers, imports and local proof commands added. |
| Sheaf.Paper.CartesianCoefficients | not queried; unchanged | Identical public theorem and coefficient definitions. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | not queried; unchanged | Identical public theorem and coefficient definitions. |
| Sheaf.Paper.QlbarTailFiniteFreeAlgebraPresentation | not queried; unchanged | Identical public theorem and coefficient definitions. |

## Status

landed 20261023T230503-L-3433485 2026-10-23 (merge of deliver/B9/Sheaf.Paper.CartesianCoefficientsFiniteFree)
