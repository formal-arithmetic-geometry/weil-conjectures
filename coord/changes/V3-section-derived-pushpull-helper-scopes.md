# Sheaf.Paper.SectionDerivedPushpullNormalization helper scopes

## Reason

Stage-3 preflight classifies new scoped `variable` commands as a change to the public
command surface and requires this record. They supply parameters only to private proved
helpers in the new `RightSquare` and `MateSquare` sections. Both sections end before the
existing public namespace and its unchanged coefficient variables. All new declarations
are private; neither public declaration changes its signature or definition. The extra
elaboration option applies only while compiling this module and is not an imported option.

The main theorem's formerly sorried proof is now complete. This record documents the static
command-surface classification, not a mathematical statement or definition change.

## Old

There were no helper sections or generic helper variables before the existing namespace:

```lean
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]
```

## New

The existing namespace and variables above remain verbatim. Added elaboration option:

```lean
set_option backward.defeqAttrib.useBackward true
```

Added section headers and parameters, verbatim:

```lean
section RightSquare

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesKInjectiveComplexes]

```

```lean
section MateSquare

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C]
  {L : B ⥤ A} {R : A ⥤ B} {L' : D ⥤ C} {R' : C ⥤ D}
  (G : B ⥤ D) (H : A ⥤ C)
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
  [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesKInjectiveComplexes]

```

Each section contains only private helper declarations and ends with its matching
`end RightSquare` or `end MateSquare`. Their parameters cannot leak into the existing
public namespace. The existing public theorem statement was compared byte-for-byte.

## Users

`tools/downstream.py Sheaf.Paper.SectionDerivedPushpullNormalization --uses
sectionDerivedPushpullNormalization normalizationInternalAdjunction` lists these nine
consumers. None mentions either declaration; both names occur only in the item module.
No consumer needs an adaptation because no public signature, definition, instance,
attribute or public import changes. Claims checked on 2026-10-22: all nine are unclaimed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.SectionDerivedTensorNormalization | unclaimed | No interface change; no adaptation. |

## Status

landed 20261021T214911-L-1885805 2026-10-21 (merge of deliver/V3/Sheaf.Paper.SectionDerivedPushpullNormalization)
