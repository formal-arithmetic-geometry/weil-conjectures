# Sheaf.CategoryTheory.LocalizationInverseImageCoherence proof context

## Reason

Complete the two original unit-normalized comparison proofs by sequential colimits.
The packet adds private proved helpers and proof-only imports. It does not change any
existing declaration signature, universe, visibility, public import, or definition body.
This record makes the additional proof context available to the independent reviewer.

## Old

The existing module-level elaboration options are:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
```

The two comparison theorem bodies are `by sorry`. There are no private
`LocalizationSequence` or `LocalizationRings` helper namespaces.

## New

The existing options remain. The new private helper namespaces additionally use:

```lean
set_option linter.unusedSectionVars false
```

The private ring helpers and the final ring comparison proof also use this scoped option:

```lean
set_option backward.isDefEq.respectTransparency.types false
```

The helpers construct normalized sequential colimit cocones for regular-module,
module-tensor and ring localizations; transport those cocones through inverse image;
and prove the resulting comparisons, including uniqueness. The ring helpers construct
ring morphisms directly using finite-product comparisons and the supplied graph equations.
Every private helper is proved. All new imports are ordinary `import`, not `public import`.
The public definitions retain their original bodies verbatim.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.LocalizationInverseImageCoherence | A4 | Two proof bodies completed; private proof context added. |
| All downstream importers | various | Public API and definitions are unchanged; no adaptation is required. |

## Status

landed 20261020T150635-L-2550220 2026-10-20 (merge of deliver/A4/Sheaf.CategoryTheory.LocalizationInverseImageCoherence)
