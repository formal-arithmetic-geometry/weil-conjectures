# Sheaf.AlgebraicGeometry.DerivedImmersionComparisonNormalization

## Reason

Stage 3 proof completion adds seven fully proved private helpers for exact derived
adjunction and square calculations. The static interface check also notices the
additional universe, option, namespace and local instance commands supporting these
helpers. No public signature or definition body changes. All public imports remain
verbatim; changed imports are private proof imports only.

## Old

The original top-level context was:

```lean
set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale
```

## New

The new context adds backward definitional-equality options and universes used only
in private generic helpers, followed by a closed helper namespace:

```lean
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v h w u

open CategoryTheory Limits

namespace CategoryTheory

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

Seven proved private helpers occur in this namespace, with two under the nested
`Functor` namespace. Both namespaces are closed before the original
`namespace AlgebraicGeometry.ProEtale` begins. The local instance attribute is
scoped to the helper namespace; the options affect elaboration in this file only.
No helper occurs in a public signature or public definition body. Existing 12 public
declaration signatures are textually identical to the originals. The five original
sorry theorem bodies are replaced with complete proofs; no sorry is added.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedImmersionComparisonNormalization | D5 | Own proof completion; public interface unchanged |

Source search finds no current Lean importers or external uses of the item
module's declarations. Its DAG parent remains attached and is not withdrawn.
No consumer adaptations are necessary because all public signatures and definition
bodies remain unchanged.

## Status

landed 20261021T152303-L-1846132 2026-10-21 (merge of deliver/D5/Sheaf.AlgebraicGeometry.DerivedImmersionComparisonNormalization)
