# AlgebraicGeometry.ProEtale.properIdentityOpenSiteComparison

## Reason

The proof uses two proved private categorical helpers. Added `open CategoryTheory.Limits`
and local instances for preservation of finite limits and finite colimits by composite
functors. Stage-3 preflight conservatively flags these top-level commands as an interface
change. This record documents their scope: the attribute is explicitly local; the open
command only resolves names in this file; helper declarations are private. No existing
public signature, definition body, public import, instance or attribute is changed.

## Old

```lean
open CategoryTheory

namespace AlgebraicGeometry.ProEtale
```

## New

```lean
open CategoryTheory

open CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

Two proved private lemmas follow these commands before the unchanged public namespace.
The theorem proof uses three declaration-scoped options:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
```

These options also precede the private descent helper, each scoped to its declaration.
Existing statements and definitions are verbatim. These changes only assist elaboration
of the completed proof and do not change its proposition or the canonical maps it uses.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ProperIdentityOpenSiteComparison
--uses properIdentityOpenSiteComparison` reports zero downstream modules and one use in
the assigned module itself. No consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperIdentityOpenSiteComparison | J5 | Own proof completed; existing interface unchanged. |

## Status

landed 20261023T123642-L-1229419 2026-10-23 (merge of deliver/J5/Sheaf.AlgebraicGeometry.ProperIdentityOpenSiteComparison)
