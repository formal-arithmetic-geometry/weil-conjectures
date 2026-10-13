# OpenUnionRestrictionTransport local elaboration attributes

## Reason

The transport proof repeatedly unfolds the localization construction when comparing
concrete derived restriction functors. Its long dependent existential elimination also
exceeds the single-file time limit. The proof now preserves the existential witnesses
with `Exists.imp` and performs the component calculation abstractly. Local reducibility
attributes keep the derived-functor and comparison constructions closed during
elaboration, with dedicated exactness instances replacing the previous generic overrides.

Preflight classifies changes to any attribute command as interface changes, including
these explicitly local commands. This record documents that classification. No declaration
signature, definition, global attribute, or importer-visible instance changes. No target
meaning changes, and no dependent module needs adaptation.

## Old

```lean
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
```

## New

```lean
attribute [local irreducible] Functor.mapDerivedCategory schemeDerivedOpenRestrictionCompIso
```

Both commands are local to the namespace in the item module. The definitions of
`Functor.mapDerivedCategory` and `schemeDerivedOpenRestrictionCompIso` are unchanged.
The signature of `AlgebraicGeometry.Scheme.open_union_restriction_transport` is
byte-identical to its original signature; only its proof changes.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.OpenUnionRestrictionTransport --uses
open_union_restriction_transport` lists these two declaration users. Its broader import
closure contains 435 modules; none sees the local attribute configuration.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OpenUnionRestrictionTransport | P3 | Proof elaboration only; unchanged signature. |
| Sheaf.AlgebraicGeometry.OpenUnionHomGluing | unclaimed | Unchanged theorem and import interface; no adaptation. |

## Status

landed 20261013T132435-L-4128175 2026-10-13 (merge of deliver/P3/Sheaf.AlgebraicGeometry.OpenUnionRestrictionTransport)
