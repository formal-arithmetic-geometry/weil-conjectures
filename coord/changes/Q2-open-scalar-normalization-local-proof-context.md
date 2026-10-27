# AlgebraicGeometry.ProEtale.CondensedRing.open_scalar_conjugate_normalization

## Reason

Prove the assigned theorem from the existing internal K-flat normalization. The
proof constructs the four auxiliary section-module derived categories through
`HasDerivedCategory.ofIsGrothendieckAbelian`. Repeated unfolding of their large
localization data during concrete mates calculations exhausted the heartbeat
budget. Keep localization construction data locally irreducible and check the
categorical calculation in proved private helpers. The final module compiles
without warnings in 14.5 seconds at the default heartbeat limit and 60-second
file limit. No definition, public signature, public import or exported attribute
changes. This record is supplied because preflight conservatively classifies a
local attribute command as an interface change.

## Old

No additional local irreducibility command. The public theorem statement is
identical to the repository version; its body was `by sorry`.

## New

```lean
-- Keep localization construction data folded while using the normalized mate.
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
```

The command is local to this module. Both existing localization constructions
retain their exact definitions, signatures, visibility and global reducibility.
The public theorem now has a complete proof, using the already stated uniquely
normalized comparison. Three private helpers are proved, with no holes.

## Users

`tools/downstream.py Sheaf.SixFunctors.OpenScalarConjugateNormalization --uses
AlgebraicGeometry.ProEtale.CondensedRing.open_scalar_conjugate_normalization`
reports the following two downstream modules and the declaration's own module.
Neither downstream source mentions the proved theorem; both keep identical
interfaces and require no edits. Public imports are unchanged, and local
irreducibility does not affect importers or target meanings.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.OpenScalarConjugateNormalization | Q2 | Proof completed; identical statement and public imports. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed | Identical public API and exported attributes; no adaptation. |
| Sheaf.SixFunctors.OpenStarShriekScalarMateSquare | unclaimed | Identical public API and exported attributes; no adaptation. |

## Status

landed 20261023T151918-L-422906 2026-10-23 (merge of deliver/Q2/Sheaf.SixFunctors.OpenScalarConjugateNormalization)
