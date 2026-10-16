# AlgebraicGeometry.ProEtale.CondensedRing.derived_nsmul_isIso

## Reason

The existing private theorem in `Sheaf.Paper.ContinuousConstructibleIntegralImage` already proves the scalar-invertibility
fact needed by the localization telescope. The second reader removed the duplicate
new module and now reuses this theorem. Exposed cocone definitions cannot refer to
a private theorem, so make the existing theorem public. The supplying module is
unclaimed. This is a visibility-only change: its binders, conclusion and proof stay
byte-identical, and no definition or target changes meaning. The module's public
imports stay unchanged. No adaptation of any other existing module is necessary.

## Old

```lean
private theorem derived_nsmul_isIso (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))) :
    IsIso (ℓ • 𝟙 K)
```

## New

```lean
theorem derived_nsmul_isIso (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))) :
    IsIso (ℓ • 𝟙 K)
```

## Users

`python3 tools/downstream.py Sheaf.Paper.ContinuousConstructibleIntegralImage --uses module_nsmul_isIso derived_nsmul_isIso`
lists the nine downstream modules below and finds uses of the helper names only in
the supplying module. Repository-wide `rg` confirms this. The new delivery modules
that directly use these theorems are also listed. All existing downstream statements
and definitions remain unchanged; this theorem-visibility change introduces no new
axiom and changes no data, so no target statement review is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Expose the existing theorem; its type and proof are unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No occurrence of either helper; statements, definitions and proofs are unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No occurrence of either helper; statements, definitions and proofs are unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No occurrence of either helper; statements, definitions and proofs are unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | C4 | No occurrence of either helper; statements, definitions and proofs are unchanged. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No occurrence of either helper; statements, definitions and proofs are unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No occurrence of either helper; statements, definitions and proofs are unchanged. |
| TargetsCheck | unclaimed | No occurrence of either helper; statements, definitions and proofs are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No occurrence of either helper; statements, definitions and proofs are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No occurrence of either helper; statements, definitions and proofs are unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalization | B2 (this delivery) | Reuse the same scalar theorem; no mathematical hypothesis changes. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | B2 (this delivery) | Reuse the same scalar theorem; no mathematical hypothesis changes. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | B2 (this delivery) | Reuse the same scalar theorem; no mathematical hypothesis changes. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | B2 (this delivery) | Reuse the same scalar theorem; no mathematical hypothesis changes. |
| Sheaf.Paper.ContinuousIntegralPushComparison | B2 (this delivery) | Reuse the same scalar theorem; no mathematical hypothesis changes. |

## Status

landed 20261016T064220-L-581729 2026-10-16 (merge of deliver/B2/Sheaf.Paper.ContinuousIntegralPushComparison)
