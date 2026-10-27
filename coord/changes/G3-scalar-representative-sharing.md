# scalarExtensionRepresentative

## Reason

Add a generic form of the existing cochain formula, with the functor and adjunction endpoints
shared before specialization. Reviewer fix (2026-10-25, re-applied 2026-10-26 on 95241d81 and again on 709c94b5): the body of
`scalarExtensionRepresentative` is NOT changed; it keeps its published formula byte for byte.
The delivered version had replaced it by an application of the new abbrev, which broke the
direct importers `Sheaf.Paper.ExceptionalCoefficientMaps` (lines 452, 605) and
`Sheaf.SixFunctors.EtaleHomComparisonModels` (line 320): their
`unfold scalarExtensionRepresentative; rw [← mapComplex_unit_formula]` no longer matched.
The only change to this module is the new abbrev `scalarAdjunctionRepresentativeMap` (and the
file-local `set_option Elab.async false`); the item proves the agreement of the specialized
abbrev with `scalarExtensionRepresentative` locally. This avoids expensive repeated comparisons of
site-specific derived-category and monoidal instances when proving the scalar/single and unit
normalizations. No target statement, hypothesis or mathematical comparison changes.

## Old

```lean
/-- The derived-extension counit on a cochain representative, including the quotient factor.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarExtensionRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (scalarExtension φ T).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) :=
  ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).homEquiv _ _).symm
    (_root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex
            (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ProEtale.etaleSheafExtendScalars φ T ⋙
              Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).inv.app P) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P))
```

## New

```lean
section Representative

variable {C : Type v} {D : Type w} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) (R : D ⥤ C) [F.Additive] [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (adj : F ⊣ R) (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
  (ad : E ⊣ R.mapDerivedCategory)

/-- The cochain adjunction transpose, sharing ordinary and derived functor endpoints.
Source: Stacks 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
abbrev scalarAdjunctionRepresentativeMap (P : CochainComplex C ℤ) :
    E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
  (ad.homEquiv _ _).symm
    (_root_.DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).inv.app P) ≫
      R.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P))

end Representative

```

`scalarExtensionRepresentative` is unchanged. The helper is an `abbrev` whose specialization
unfolds to the same adjunction transpose. No object is selected from a mere existence assertion.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.BoundedFlatCoefficientSiteSquare | J2 | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.EtaleDerivedScalarTensor | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | H1 | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.EtaleProEtaleScalarMate | T7 | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.EtaleSumCoefficientComputation | W8 | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.EtaleSystemCofinalMate | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.ExceptionalCoefficientMaps | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.ExceptionalCoefficientUnitCoherence | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.FiniteFreeHomLocalCalculation | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.FiniteHomDomainCalculus | G7 | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.PurEtaleScalarMateProjection | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.ScalarPullbackIsoExistence | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.ScalarPullbackIsoUniqueness | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.Paper.ScalarTensorPullbackNormalization | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.SixFunctors.EtaleHomComparisonModels | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenTensorDefs | unclaimed | Definition unchanged; only a new declaration is added; no adaptation. |

The 709c94b5 delivery also carried `scalarRepresentativeUnit` and the private
`scalarExtensionRepresentative_unit` of the T7 landing 68e7567cd43. That landing was taken out of
`sheaf-dag` by 73427fd8534 (it broke an importer); the reviewer fix does not reintroduce these
T7 declarations. The module is the current published file plus the abbrev only.

## Status

landed 20261025T202103-L-2672233 2026-10-25 (merge of deliver/G3/Sheaf.Paper.FiniteTateScalarSourceNormalization)
