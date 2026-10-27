# AlgebraicGeometry.ProEtale.CondensedRing.moduleDerivedCompositor

## Reason

The completed proofs require Lean to recognize the canonical identities between mapped
complexes and composite mapped functors. Two elaboration transparency options permit
this recognition. A single theorem-local linter option suppresses the warning for its
inherited, unchanged commutative-ring parameter. Preflight classifies the addition of
these commands as a visible-command change and requires this record. No declaration
signature, definition body, public import, instance, notation, or attribute changes.

## Old

The original file has the following options:

```lean
set_option autoImplicit false
```

The identity-normalization theorem is declared without a local lint option.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Immediately before the unchanged docstring and declaration of
`module_derived_identity_normalization`:

```lean
set_option linter.unusedSectionVars false in
```

These options control elaboration of this file and do not export changes to importers.
All seven public declaration signatures and the bodies of all three definitions are
verbatim unchanged. The four theorem proofs are completed, with no remaining holes.
Private proof imports and private proved helpers are added; six unused private proof
imports are removed. No target or definition used by a target changes meaning.

## Users

`tools/downstream.py Sheaf.Paper.ModuleDerivedCompositorCoherence --uses
moduleDerivedCompositor` and the same command for `moduleDerivedIdentity` report the
four downstream modules below and the two direct declaration users. The only direct
importer is IdentityOpenDerivedRestriction; the other users import transitively.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleDerivedCompositorCoherence | M5 | Four proof holes closed; API unchanged. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | F5 | Unchanged consumer; no adaptation needed. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | E8 | Transitive importer; no adaptation. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Transitive importer; no adaptation. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Uses both canonical comparisons; identical signatures and definition bodies. |

The consumer's original source is compiled separately against the delivered dependency
in the sandbox, then excluded from the delivery. No held consumer file is modified.

## Status

landed 20261023T151855-L-418610 2026-10-23 (merge of deliver/M5/Sheaf.Paper.ModuleDerivedCompositorCoherence)
