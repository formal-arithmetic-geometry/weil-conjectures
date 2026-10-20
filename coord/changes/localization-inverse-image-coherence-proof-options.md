# Sheaf.CategoryTheory.LocalizationInverseImageCoherence proof context

## Reason

The stage-3 checker treats the completed proof context as an interface change.
This record submits that context to independent review. All public declaration
signatures, definitions, universes and visibility stay unchanged. The new private
helpers are proved, and the imports needed only for proofs remain private imports.

## Old

The module contained `set_option autoImplicit false`, the namespace and its public
statements. It had no private universe-presentation or derived-transformation helpers.

## New

The module also uses these elaboration options:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
```

Private helpers convert the existing inverse-image presentation between universe
conventions, prove scalar-localization exactness, and localize arbitrary natural
transformations with left/right whiskering equations. They are used only in proofs.
The `open MonoidalCategory in` command scopes the scalar-exactness proof. These
commands introduce no public notation, instance, definition or theorem signature.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.LocalizationInverseImageCoherence | Y7 | Proof context and five proof bodies change; public API unchanged. |
| All downstream importers | various | No signature or definition change; no consumer adaptation is required. The proof-context commands do not change their mathematical statements. |

## Status

landed 20261020T131238-L-1265414 2026-10-20 (merge of deliver/Y7/Sheaf.CategoryTheory.LocalizationInverseImageCoherence)
