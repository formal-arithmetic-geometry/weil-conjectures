# WeilConjectures.CompletedStalk.derivedSectionRestriction

## Reason

The full item exceeded the 60-second compilation limit. Profiling attributed
34.3 seconds of kernel checking to the existing derived restriction construction.
Its scheme map was concretely `sourceIso D α` throughout several derived-functor
and preservation-instance conversions.

Factor the same expression through a local `construction` parameterized by
abelian categories, exact functors `F` and `G`, and an isomorphism `ρ : F ≅ G ⋙ F`.
Apply it to the original sections and inverse-image functors and to
`sectionRestriction D l E α`, retaining every original local instance and explicitly selecting the same
standard source localization as the existing library.
Beta/zeta reduction returns the old expression exactly (up to proof irrelevance
of typeclass proofs).
All maps, instances, the public signature, universes and visibility are preserved.
This changes elaboration/kernel workload, not the mathematical definition.
No target has a changed meaning; target statement review is therefore a
verification of this definitional equality, with no statement amendment requested.

## Old

```lean
def derivedSectionRestriction (α : D.k ≃+* D.k) :
    pointFibreIntegralAmbient D l E ≅
      AlgebraicGeometry.ProEtale.inverseImageIntegralDerived l E (sourceIso D α).hom ⋙
        pointFibreIntegralAmbient D l E :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI := pointIntegralSectionsAdditive l E D.k
  letI := isoSectionwiseModuleInverseImage_additive (sourceIso D α).hom
    (AlgebraicGeometry.ProEtale.inverseImageCompletedCoefficientMap l E (sourceIso D α).hom)
  letI := pointFibreIntegralLimits D l E
  letI := pointFibreIntegralColimits D l E
  letI := isoSectionwiseModuleInverseImage_limits (sourceIso D α).hom
    (AlgebraicGeometry.ProEtale.inverseImageCompletedCoefficientMap l E (sourceIso D α).hom)
  letI := isoSectionwiseModuleInverseImage_colimits (sourceIso D α).hom
    (AlgebraicGeometry.ProEtale.inverseImageCompletedCoefficientMap l E (sourceIso D α).hom)
  Functor.mapDerivedCategoryNatIso (sectionRestriction D l E α) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
```

## New

```lean
def derivedSectionRestriction (α : D.k ≃+* D.k) :
    pointFibreIntegralAmbient D l E ≅
      AlgebraicGeometry.ProEtale.inverseImageIntegralDerived l E (sourceIso D α).hom ⋙
        pointFibreIntegralAmbient D l E :=
  letI : HasDerivedCategory.{u + 2} (integralTowerModules l E (Spec (.of D.k))) :=
    integralTowerHasDerivedCategory l E (Spec (.of D.k))
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI := pointIntegralSectionsAdditive l E D.k
  letI := isoSectionwiseModuleInverseImage_additive (sourceIso D α).hom
    (AlgebraicGeometry.ProEtale.inverseImageCompletedCoefficientMap l E (sourceIso D α).hom)
  letI := pointFibreIntegralLimits D l E
  letI := pointFibreIntegralColimits D l E
  letI := isoSectionwiseModuleInverseImage_limits (sourceIso D α).hom
    (AlgebraicGeometry.ProEtale.inverseImageCompletedCoefficientMap l E (sourceIso D α).hom)
  letI := isoSectionwiseModuleInverseImage_colimits (sourceIso D α).hom
    (AlgebraicGeometry.ProEtale.inverseImageCompletedCoefficientMap l E (sourceIso D α).hom)
  let construction {A B : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
      [Abelian A] [Abelian B]
      [HasDerivedCategory.{u + 2} A] [HasDerivedCategory.{u + 1} B]
      (F : A ⥤ B) (G : A ⥤ A) [F.Additive] [G.Additive]
      [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      [PreservesFiniteLimits G] [PreservesFiniteColimits G] (ρ : F ≅ G ⋙ F) :
      F.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ F.mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryCompIso G F
  construction (pointIntegralSections l E D.k)
    (AlgebraicGeometry.ProEtale.inverseImageIntegralModules l E (sourceIso D α).hom)
    (sectionRestriction D l E α)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | S2 | The only textual user is its own `sectionMap`; its definition is unchanged and the refactor is definitionally equal. |

A whole-library search for `derivedSectionRestriction` finds no external user.
The six direct importers are `Sheaf.TraceFormula.PointConeLiftsChainNaturality`,
`Sheaf.Paper.PointPullbackConeLocalization`,
`Sheaf.Paper.PointTransportResolutionCancellation`,
`Sheaf.Paper.PointSectionsCompletionCone`,
`Sheaf.Paper.PointTransportConeComparisonDescent`, and
`Sheaf.Paper.NormalizedFiniteFibreModels`. Their references to this module concern
other, unchanged declarations. There is no forced adaptation and no consumer
statement becomes stronger, weaker or different.

## Status

landed 20261026T070938-L-3709856 2026-10-26 (merge of deliver/S2/Sheaf.Paper.CompletedStalkReparametrizationCoherence)
