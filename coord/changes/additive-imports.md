# bottomFreeChain_pullback_comparison proof support

## Reason

Preflight classifies added `attribute` commands as a visible-interface change,
including the local instance attributes used here. These attributes are local to
this module, and the new helper is private. No public signature, definition,
docstring or public import changes, and no downstream adaptation is required.
The change record documents the exact commands rather than a mathematical
statement change. No target meaning or definition used by a target changes.

## Old

```lean
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
```

## New

```lean
set_option autoImplicit false
set_option linter.style.haveILetI false
attribute [local instance] CategoryTheory.Functor.additive_of_preserves_binary_products
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
```

These local instances allow exact restriction to act on derived categories.
The private helper `bottomFreeChain_pullback_additive` and the theorem-local
elaboration options support the proof. Existing declaration signatures are
byte-for-byte unchanged. The new derived-square theorem has its own DAG node.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BottomFreeChainPullbackComparison | R2 | local proof elaboration only |

The attributes are local and the helper private, so no downstream module can
observe a changed declaration or instance. There is no declaration whose
signature changes and therefore no forced adaptation or affected target.

## Status

landed 20261013T133747-L-44971 2026-10-13 (merge of deliver/R2/Sheaf.AlgebraicGeometry.BottomFreeChainPullbackComparison)
