# AlgebraicGeometry.SupportedConstantNormalization.comparePullback

## Reason

Give the existing comparison isomorphism its native module-valued source and target
as an explicit type, and retain the identical generic comparison construction as
its body. The abbreviation previously exposed the constructed site functors in
section-evaluation types; converting those through chosen sheafification limits
caused the section diagram to exceed the kernel checking limit. The native type
keeps the inverse-image functors named. No canonical map, hypothesis, coefficient
universe, or normalization changes. The definition is reached by targets and is
flagged for independent statement review.

## Old

```lean
abbrev comparePullback {X' X : Scheme.{u}} (h : X' ⟶ X) :=
  ProEtale.supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) h
```

## New

```lean
def comparePullback {X' X : Scheme.{u}} (h : X' ⟶ X) :
    pull A false h ⋙ compare A X' ≅ compare A X ⋙ pull A true h :=
  ProEtale.supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) h
```

## Users

The source scan lists four explicit users and 134 transitive downstream modules.
The constructed isomorphism is definitionally identical. No consumer adaptation
is required; all existing declaration signatures are preserved. Claim records
were read on 2026-10-25.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization | unclaimed | Same comparison with a native typed interface. |
| Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison | J5 | Section diagram uses the native module-valued interface. |
| Sheaf.Paper.SectionSupportedComparisonIso | unclaimed | Definitionally identical comparison; no adaptation. |
| Sheaf.Paper.SectionSupportedProExchangeIso | unclaimed | Definitionally identical comparison; no adaptation. |

## Status

landed 20261026T001858-L-37735 2026-10-26 (merge of deliver/J5/Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison)
