# CategoryTheory.Functor.normalizedDerivedComparison_composition

## Reason

The first stage-3 preflight requested a change record because the proof adds section
variables, options and a local attribute. This records their exact scope. No public
statement, existing definition, public import, or visibility changes. No consumer
adaptation or target statement review is required: existing declarations have exactly
the same types and meanings.

## Old

The existing public theorem signature, verbatim:

```lean
theorem normalizedDerivedComparison_composition
    {A0 : Type uA0} {A1 : Type uA1} {A2 : Type uA2}
    {B0 : Type uB0} {B1 : Type uB1} {B2 : Type uB2}
    [Category.{vA0} A0] [Category.{vA1} A1] [Category.{vA2} A2]
    [Category.{vB0} B0] [Category.{vB1} B1] [Category.{vB2} B2]
    [Abelian A0] [Abelian A1] [Abelian A2] [Abelian B0] [Abelian B1] [Abelian B2]
    [HasDerivedCategory.{wA0} A0] [HasDerivedCategory.{wA1} A1]
    [HasDerivedCategory.{wA2} A2] [HasDerivedCategory.{wB0} B0]
    [HasDerivedCategory.{wB1} B1] [HasDerivedCategory.{wB2} B2]
    (F0 : A0 ⥤ B0) (F1 : A1 ⥤ B1) (F2 : A2 ⥤ B2)
    [F0.Additive] [F1.Additive] [F2.Additive]
    (enough0 : ∀ K : CochainComplex A0 ℤ,
      ∃ (I : CochainComplex A0 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enough1 : ∀ K : CochainComplex A1 ℤ,
      ∃ (I : CochainComplex A1 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enough2 : ∀ K : CochainComplex A2 ℤ,
      ∃ (I : CochainComplex A2 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (r01 : A1 ⥤ A0) (r12 : A2 ⥤ A1) (r02 : A2 ⥤ A0)
    (s01 : B1 ⥤ B0) (s12 : B2 ⥤ B1) (s02 : B2 ⥤ B0)
    [r01.Additive] [r12.Additive] [r02.Additive]
    [s01.Additive] [s12.Additive] [s02.Additive]
    [PreservesFiniteLimits r01] [PreservesFiniteColimits r01]
    [PreservesFiniteLimits r12] [PreservesFiniteColimits r12]
    [PreservesFiniteLimits r02] [PreservesFiniteColimits r02]
    [PreservesFiniteLimits s01] [PreservesFiniteColimits s01]
    [PreservesFiniteLimits s12] [PreservesFiniteColimits s12]
    [PreservesFiniteLimits s02] [PreservesFiniteColimits s02]
    (er : r02 = r12 ⋙ r01) (es : s02 = s12 ⋙ s01)
    (e01 : r01 ⋙ F0 = F1 ⋙ s01) (e12 : r12 ⋙ F1 = F2 ⋙ s12)
    (e02 : r02 ⋙ F0 = F2 ⋙ s02)
    (β01 : r01.mapDerivedCategory ⋙ F0.rightDerivedFunctorOfQuasiIsoResolutions enough0 ≅
      F1.rightDerivedFunctorOfQuasiIsoResolutions enough1 ⋙ s01.mapDerivedCategory)
    (β12 : r12.mapDerivedCategory ⋙ F1.rightDerivedFunctorOfQuasiIsoResolutions enough1 ≅
      F2.rightDerivedFunctorOfQuasiIsoResolutions enough2 ⋙ s12.mapDerivedCategory)
    (β02 : r02.mapDerivedCategory ⋙ F0.rightDerivedFunctorOfQuasiIsoResolutions enough0 ≅
      F2.rightDerivedFunctorOfQuasiIsoResolutions enough2 ⋙ s02.mapDerivedCategory)
    (h01 : IsKInjectiveNormalizedDerivedComparison F0 F1 r01 s01 e01 enough0 enough1 β01)
    (h12 : IsKInjectiveNormalizedDerivedComparison F1 F2 r12 s12 e12 enough1 enough2 β12)
    (h02 : IsKInjectiveNormalizedDerivedComparison F0 F2 r02 s02 e02 enough0 enough2 β02)
    (L : DerivedCategory A2) :
    β02.hom.app L =
      (F0.rightDerivedFunctorOfQuasiIsoResolutions enough0).map
        ((normalizedDerivedComparisonCompositionLocalizationIso r02 r12 r01 er).hom.app L) ≫
      β01.hom.app (r12.mapDerivedCategory.obj L) ≫
      s01.mapDerivedCategory.map (β12.hom.app L) ≫
      (normalizedDerivedComparisonCompositionLocalizationIso s02 s12 s01 es).inv.app
        ((F2.rightDerivedFunctorOfQuasiIsoResolutions enough2).obj L)
```

There was no `UnitSquare` or `CompositionFactors` section and no private helper.

## New

The public theorem signature is unchanged, verbatim:

```lean
theorem normalizedDerivedComparison_composition
    {A0 : Type uA0} {A1 : Type uA1} {A2 : Type uA2}
    {B0 : Type uB0} {B1 : Type uB1} {B2 : Type uB2}
    [Category.{vA0} A0] [Category.{vA1} A1] [Category.{vA2} A2]
    [Category.{vB0} B0] [Category.{vB1} B1] [Category.{vB2} B2]
    [Abelian A0] [Abelian A1] [Abelian A2] [Abelian B0] [Abelian B1] [Abelian B2]
    [HasDerivedCategory.{wA0} A0] [HasDerivedCategory.{wA1} A1]
    [HasDerivedCategory.{wA2} A2] [HasDerivedCategory.{wB0} B0]
    [HasDerivedCategory.{wB1} B1] [HasDerivedCategory.{wB2} B2]
    (F0 : A0 ⥤ B0) (F1 : A1 ⥤ B1) (F2 : A2 ⥤ B2)
    [F0.Additive] [F1.Additive] [F2.Additive]
    (enough0 : ∀ K : CochainComplex A0 ℤ,
      ∃ (I : CochainComplex A0 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enough1 : ∀ K : CochainComplex A1 ℤ,
      ∃ (I : CochainComplex A1 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enough2 : ∀ K : CochainComplex A2 ℤ,
      ∃ (I : CochainComplex A2 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (r01 : A1 ⥤ A0) (r12 : A2 ⥤ A1) (r02 : A2 ⥤ A0)
    (s01 : B1 ⥤ B0) (s12 : B2 ⥤ B1) (s02 : B2 ⥤ B0)
    [r01.Additive] [r12.Additive] [r02.Additive]
    [s01.Additive] [s12.Additive] [s02.Additive]
    [PreservesFiniteLimits r01] [PreservesFiniteColimits r01]
    [PreservesFiniteLimits r12] [PreservesFiniteColimits r12]
    [PreservesFiniteLimits r02] [PreservesFiniteColimits r02]
    [PreservesFiniteLimits s01] [PreservesFiniteColimits s01]
    [PreservesFiniteLimits s12] [PreservesFiniteColimits s12]
    [PreservesFiniteLimits s02] [PreservesFiniteColimits s02]
    (er : r02 = r12 ⋙ r01) (es : s02 = s12 ⋙ s01)
    (e01 : r01 ⋙ F0 = F1 ⋙ s01) (e12 : r12 ⋙ F1 = F2 ⋙ s12)
    (e02 : r02 ⋙ F0 = F2 ⋙ s02)
    (β01 : r01.mapDerivedCategory ⋙ F0.rightDerivedFunctorOfQuasiIsoResolutions enough0 ≅
      F1.rightDerivedFunctorOfQuasiIsoResolutions enough1 ⋙ s01.mapDerivedCategory)
    (β12 : r12.mapDerivedCategory ⋙ F1.rightDerivedFunctorOfQuasiIsoResolutions enough1 ≅
      F2.rightDerivedFunctorOfQuasiIsoResolutions enough2 ⋙ s12.mapDerivedCategory)
    (β02 : r02.mapDerivedCategory ⋙ F0.rightDerivedFunctorOfQuasiIsoResolutions enough0 ≅
      F2.rightDerivedFunctorOfQuasiIsoResolutions enough2 ⋙ s02.mapDerivedCategory)
    (h01 : IsKInjectiveNormalizedDerivedComparison F0 F1 r01 s01 e01 enough0 enough1 β01)
    (h12 : IsKInjectiveNormalizedDerivedComparison F1 F2 r12 s12 e12 enough1 enough2 β12)
    (h02 : IsKInjectiveNormalizedDerivedComparison F0 F2 r02 s02 e02 enough0 enough2 β02)
    (L : DerivedCategory A2) :
    β02.hom.app L =
      (F0.rightDerivedFunctorOfQuasiIsoResolutions enough0).map
        ((normalizedDerivedComparisonCompositionLocalizationIso r02 r12 r01 er).hom.app L) ≫
      β01.hom.app (r12.mapDerivedCategory.obj L) ≫
      s01.mapDerivedCategory.map (β12.hom.app L) ≫
      (normalizedDerivedComparisonCompositionLocalizationIso s02 s12 s01 es).inv.app
        ((F2.rightDerivedFunctorOfQuasiIsoResolutions enough2).obj L)
```

The added section-variable context is:

```lean
section UnitSquare

variable
    {A : Type u0} {A' : Type u1} {B : Type u2} {B' : Type uB0}
    [Category.{v0} A] [Category.{v1} A'] [Category.{v2} B] [Category.{vB0} B']
    [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
    [HasDerivedCategory.{w0} A] [HasDerivedCategory.{w1} A']
    [HasDerivedCategory.{w2} B] [HasDerivedCategory.{wB0} B']
    (F : A ⥤ B) (G : A' ⥤ B') [F.Additive] [G.Additive]
    (r : A' ⥤ A) (s : B' ⥤ B) [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (e : r ⋙ F = G ⋙ s)
    (enoughA : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enoughA' : ∀ K : CochainComplex A' ℤ,
      ∃ (I : CochainComplex A' ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (β : r.mapDerivedCategory ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions enoughA ≅
      G.rightDerivedFunctorOfQuasiIsoResolutions enoughA' ⋙ s.mapDerivedCategory)
```

This section ends before `section CompositionFactors`; all declarations within it are
private proved helpers. No section variable is auto-bound and none adds a binder to
an existing declaration. `CompositionFactors` adds exactly this local command:

```lean
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

The section ends before the existing public theorem. Thus the attribute is no longer
active at that theorem and is not exported. The file also enables the standard
elaboration options `backward.isDefEq.respectTransparency`,
`backward.isDefEq.respectTransparency.types` (both false), and
`backward.defeqAttrib.useBackward` (true) for the new proof calculations. These are
file-local elaboration settings, not exported attributes or instances.

The added `comparisonUnit` is a private construction of the natural unit on complexes
from the existing unit and Q/Qh identifications. Its data and naturality are completely
specified and proved. It appears only in private helper statements and theorem proofs,
never in a public signature or public definition. Every added private theorem is proved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.NormalizedDerivedComparisonComposition | T9 | Private proof helpers and completed proof; existing public interfaces unchanged. |

A whole-library source search found no importer and no external textual user of
`normalizedDerivedComparison_composition`. The assignment remains needed through the
DAG of unfinished parents; no withdrawal is proposed. All DAG statement attachments
and the target statements are preserved.

## Status

landed 20261021T120659-L-3932609 2026-10-21 (merge of deliver/T9/Sheaf.CategoryTheory.NormalizedDerivedComparisonComposition)
