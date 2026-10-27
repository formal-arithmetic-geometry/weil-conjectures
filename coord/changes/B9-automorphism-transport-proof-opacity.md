# AlgebraicGeometry.Scheme.pbcIsoModulePullback_isEquivalence

## Reason

The completed ordinary-pullback and derived-localization definitions were
repeatedly unfolded while elaborating the normalized derived-comparison
statement. Local opacity lets Lean use their existing typed APIs. This is a
proof elaboration change only.

## Old

No local irreducibility attributes for the following declarations in this module.
Their existing definitions and public signatures are unchanged.

## New

```lean
attribute [local irreducible] proEtaleRingModulePullback completedModulePullback
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  completedPullbackComparison completedPullbackObject
  completedCoefficientMap

attribute [local irreducible] pbcIsoIntegralPullback
```

The existing integral scalar comparison is placed in a local section restoring
`semireducible` for `pbcIsoIntegralPullback` while its ambient equality is
elaborated. The linearity proof unfolds the integral lift explicitly.

These attributes expire at the end of the module. No definition body, signature,
public import, or global instance is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PbcAutomorphismTransport | B9 | Local elaboration only; three existing theorem proofs filled. |

All consumers retain the same public declarations, definitions, attributes and
imports. The attributes are local; no consumer requires adaptation.

## Status

landed 20261025T162031-L-216342 2026-10-25 (merge of deliver/B9/Sheaf.Paper.PbcAutomorphismTransport)
