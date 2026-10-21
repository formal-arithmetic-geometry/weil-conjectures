# Sheaf.AlgebraicGeometry.ComparisonDirectImageResolutionMate

## Reason

Preflight requires a change record for added `section` and `variable` commands.
The private generic base-change calculation needs four abelian categories and the
functors between them. These binders are scoped to `ResolutionBaseChange`, which
ends before the specialized helpers and original theorem. No public signature,
attribute, instance, notation, definition body, or public import changes.

## Old

No `ResolutionBaseChange` section or variables existed. No existing declaration
signature or definition is being replaced: the sole existing theorem proof was
`by sorry`. All existing signatures and all definition bodies remain verbatim.

## New

The following new local command block supplies binders only to three proved
private lemmas; it is closed by `end ResolutionBaseChange` immediately after
`baseChange_resolutions`.

```lean
section ResolutionBaseChange

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
  [HasDerivedCategory C'] [EnoughInjectives B] [EnoughInjectives B']
  (G : B ⥤ C) (G' : B' ⥤ C') (β : B ⥤ B') (γ : C ⥤ C')
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
```

The new lemmas are `resolution_baseChange_fac`, `quasiIso_plus_Q_isIso`, and
`baseChange_resolutions`; all are private and fully proved. The original theorem
is now proved using private calculation helpers. Eight unnecessary proof imports
are removed. The original unit-route import and all public imports are retained.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ComparisonDirectImageResolutionMate | W6 | Private proof helpers only; original public API unchanged. |

No downstream adaptation is necessary because there is no interface change.
No target definition or statement changes, and no target statement review is reopened.

## Status

landed 20261021T120846-L-3967977 2026-10-21 (merge of deliver/W6/Sheaf.AlgebraicGeometry.ComparisonDirectImageResolutionMate)
