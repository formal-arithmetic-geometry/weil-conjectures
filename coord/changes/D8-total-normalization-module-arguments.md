# SectionTotalNormalization

## Reason

In the two scalar clauses, give `internalPureTensor` its explicit ordinary module arguments `(CondensedRing.upperStar Λ f).obj (P.X p)` and the analogous argument for Q, instead of inferring those arguments through the projections of termwise cochain functors. These are definitionally the same arguments. No binder, universe, hypothesis or equation changes; the public theorem signature and TotalMapAgreement remain verbatim. A Lean probe states equality of the complete new proposition with the original proposition, copied verbatim, and proves it by `rfl`. Its validation is recorded in the report.

## Old

```lean
def SectionTotalNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{u + 1} (modules Λ X)] : Prop :=
  (∀ P Q : CochainComplex (internalModules Λ Y) ℤ,
    TotalMapAgreement Λ X (conjugatedInternalTotalIso Λ f P Q).hom
      (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj P)
        ((totalSectionEquivalence Λ Y).obj Q)).hom ) ∧
  (∀ P Q : CochainComplex (internalModules Λ Y) ℤ,
    TotalMapAgreement Λ X (conjugatedInternalTotalIso Λ f P Q).inv
      (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj P)
        ((totalSectionEquivalence Λ Y).obj Q)).inv ) ∧
  (∀ (P Q : CochainComplex (modules Λ Y) ℤ) (p q n : ℤ) (h : p + q = n),
    (pullback Λ f).map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (sectionTotalIso Λ f P Q).hom.f n =
      normalizationSectionTensor Λ f (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q) p q n h ) ∧
  (∀ (P Q : CochainComplex (modules Λ Y) ℤ)
      (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιTensorObj
        ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q) p q n h ≫
        (sectionTotalIso Λ f P Q).inv.f n =
      inv (normalizationSectionTensor Λ f (P.X p) (Q.X q)) ≫
        (pullback Λ f).map (HomologicalComplex.ιTensorObj P Q p q n h) ) ∧
  (∀ (P Q : CochainComplex (internalModules Λ Y) ℤ)
      (p q n : ℤ) (h : p + q = n) (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
      (x : ((normalizationInverseImage Λ f).obj (P.X p)).X.obj.obj W)
      (y : ((normalizationInverseImage Λ f).obj (Q.X q)).X.obj.obj W),
    (((CondensedRing.upperStar Λ f).map
          (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (actualInternalTotalIso Λ f P Q).hom.f n).hom.hom.app W)
        (normalizationScalarTensor Λ f (P.X p ⊗ Q.X q) W s
          (normalizationInverseImageTensor Λ f (P.X p) (Q.X q) W x y)) =
      ((HomologicalComplex.ιTensorObj
          ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q)
          p q n h).hom.hom.app W)
        (internalPureTensor Λ X _ _ W
          (normalizationScalarTensor Λ f (P.X p) W s x)
          (normalizationScalarTensor Λ f (Q.X q) W 1 y))) ∧
  (∀ (P Q : CochainComplex (internalModules Λ Y) ℤ)
      (p q n : ℤ) (h : p + q = n) (W : X.ProEtᵒᵖ) (s t : (ring Λ X).obj.obj W)
      (x : ((normalizationInverseImage Λ f).obj (P.X p)).X.obj.obj W)
      (y : ((normalizationInverseImage Λ f).obj (Q.X q)).X.obj.obj W),
    ((HomologicalComplex.ιTensorObj
          ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q) p q n h ≫
        (actualInternalTotalIso Λ f P Q).inv.f n).hom.hom.app W)
        (internalPureTensor Λ X _ _ W
          (normalizationScalarTensor Λ f (P.X p) W s x)
          (normalizationScalarTensor Λ f (Q.X q) W t y)) =
      (((CondensedRing.upperStar Λ f).map
          (HomologicalComplex.ιTensorObj P Q p q n h)).hom.hom.app W)
        (normalizationScalarTensor Λ f (P.X p ⊗ Q.X q) W (s * t)
          (normalizationInverseImageTensor Λ f (P.X p) (Q.X q) W x y))) ∧
  (TotalMapAgreement Λ X
    (conjugatedInternalTotalUnit Λ f) (sectionTotalUnit Λ f) ) ∧
  (∀ (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
      (r : ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y)).obj.obj W),
    (((actualInternalTotalUnit Λ f).f 0).hom.hom.app W)
        (normalizationScalarTensor Λ f (𝟙_ (internalModules Λ Y)) W s r) =
      s * (@id ((ring Λ X).obj.obj W) ((condensedPullbackHom Λ f).hom.app W r)) ) ∧
  (∀ (P Q P' Q' : CochainComplex (modules Λ Y) ℤ)
      (a : P ⟶ P') (b : Q ⟶ Q'),
    TotalMapAgreement Λ X
      ((totalSectionPull Λ f).map (a ⊗ₘ b) ≫ (sectionTotalIso Λ f P' Q').hom)
      ((sectionTotalIso Λ f P Q).hom ≫
        ((totalSectionPull Λ f).map a ⊗ₘ (totalSectionPull Λ f).map b)) ) ∧
  (∀ P Q H : CochainComplex (modules Λ Y) ℤ,
    TotalMapAgreement Λ X
      ((totalSectionPull Λ f).map (α_ P Q H).hom ≫
        (sectionTotalIso Λ f P (Q ⊗ H)).hom ≫
        (totalSectionPull Λ f).obj P ◁ (sectionTotalIso Λ f Q H).hom)
      ((sectionTotalIso Λ f (P ⊗ Q) H).hom ≫
        (sectionTotalIso Λ f P Q).hom ▷ (totalSectionPull Λ f).obj H ≫
        (α_ ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q)
          ((totalSectionPull Λ f).obj H)).hom) ) ∧
  (∀ P : CochainComplex (modules Λ Y) ℤ,
    TotalMapAgreement Λ X
      ((sectionTotalIso Λ f (𝟙_ (CochainComplex (modules Λ Y) ℤ)) P).hom ≫
        sectionTotalUnit Λ f ▷ (totalSectionPull Λ f).obj P ≫
        (λ_ ((totalSectionPull Λ f).obj P)).hom)
      ((totalSectionPull Λ f).map (λ_ P).hom) ) ∧
  (∀ P : CochainComplex (modules Λ Y) ℤ,
    TotalMapAgreement Λ X
      ((sectionTotalIso Λ f P (𝟙_ (CochainComplex (modules Λ Y) ℤ))).hom ≫
        (totalSectionPull Λ f).obj P ◁ sectionTotalUnit Λ f ≫
        (ρ_ ((totalSectionPull Λ f).obj P)).hom)
      ((totalSectionPull Λ f).map (ρ_ P).hom)
)

```

## New

```lean
def SectionTotalNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{u + 1} (modules Λ X)] : Prop :=
  (∀ P Q : CochainComplex (internalModules Λ Y) ℤ,
    TotalMapAgreement Λ X (conjugatedInternalTotalIso Λ f P Q).hom
      (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj P)
        ((totalSectionEquivalence Λ Y).obj Q)).hom ) ∧
  (∀ P Q : CochainComplex (internalModules Λ Y) ℤ,
    TotalMapAgreement Λ X (conjugatedInternalTotalIso Λ f P Q).inv
      (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj P)
        ((totalSectionEquivalence Λ Y).obj Q)).inv ) ∧
  (∀ (P Q : CochainComplex (modules Λ Y) ℤ) (p q n : ℤ) (h : p + q = n),
    (pullback Λ f).map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (sectionTotalIso Λ f P Q).hom.f n =
      normalizationSectionTensor Λ f (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q) p q n h ) ∧
  (∀ (P Q : CochainComplex (modules Λ Y) ℤ)
      (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιTensorObj
        ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q) p q n h ≫
        (sectionTotalIso Λ f P Q).inv.f n =
      inv (normalizationSectionTensor Λ f (P.X p) (Q.X q)) ≫
        (pullback Λ f).map (HomologicalComplex.ιTensorObj P Q p q n h) ) ∧
  (∀ (P Q : CochainComplex (internalModules Λ Y) ℤ)
      (p q n : ℤ) (h : p + q = n) (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
      (x : ((normalizationInverseImage Λ f).obj (P.X p)).X.obj.obj W)
      (y : ((normalizationInverseImage Λ f).obj (Q.X q)).X.obj.obj W),
    (((CondensedRing.upperStar Λ f).map
          (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (actualInternalTotalIso Λ f P Q).hom.f n).hom.hom.app W)
        (normalizationScalarTensor Λ f (P.X p ⊗ Q.X q) W s
          (normalizationInverseImageTensor Λ f (P.X p) (Q.X q) W x y)) =
      ((HomologicalComplex.ιTensorObj
          ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q)
          p q n h).hom.hom.app W)
        (internalPureTensor Λ X
          ((CondensedRing.upperStar Λ f).obj (P.X p))
          ((CondensedRing.upperStar Λ f).obj (Q.X q)) W
          (normalizationScalarTensor Λ f (P.X p) W s x)
          (normalizationScalarTensor Λ f (Q.X q) W 1 y))) ∧
  (∀ (P Q : CochainComplex (internalModules Λ Y) ℤ)
      (p q n : ℤ) (h : p + q = n) (W : X.ProEtᵒᵖ) (s t : (ring Λ X).obj.obj W)
      (x : ((normalizationInverseImage Λ f).obj (P.X p)).X.obj.obj W)
      (y : ((normalizationInverseImage Λ f).obj (Q.X q)).X.obj.obj W),
    ((HomologicalComplex.ιTensorObj
          ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q) p q n h ≫
        (actualInternalTotalIso Λ f P Q).inv.f n).hom.hom.app W)
        (internalPureTensor Λ X
          ((CondensedRing.upperStar Λ f).obj (P.X p))
          ((CondensedRing.upperStar Λ f).obj (Q.X q)) W
          (normalizationScalarTensor Λ f (P.X p) W s x)
          (normalizationScalarTensor Λ f (Q.X q) W t y)) =
      (((CondensedRing.upperStar Λ f).map
          (HomologicalComplex.ιTensorObj P Q p q n h)).hom.hom.app W)
        (normalizationScalarTensor Λ f (P.X p ⊗ Q.X q) W (s * t)
          (normalizationInverseImageTensor Λ f (P.X p) (Q.X q) W x y))) ∧
  (TotalMapAgreement Λ X
    (conjugatedInternalTotalUnit Λ f) (sectionTotalUnit Λ f) ) ∧
  (∀ (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
      (r : ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y)).obj.obj W),
    (((actualInternalTotalUnit Λ f).f 0).hom.hom.app W)
        (normalizationScalarTensor Λ f (𝟙_ (internalModules Λ Y)) W s r) =
      s * (@id ((ring Λ X).obj.obj W) ((condensedPullbackHom Λ f).hom.app W r)) ) ∧
  (∀ (P Q P' Q' : CochainComplex (modules Λ Y) ℤ)
      (a : P ⟶ P') (b : Q ⟶ Q'),
    TotalMapAgreement Λ X
      ((totalSectionPull Λ f).map (a ⊗ₘ b) ≫ (sectionTotalIso Λ f P' Q').hom)
      ((sectionTotalIso Λ f P Q).hom ≫
        ((totalSectionPull Λ f).map a ⊗ₘ (totalSectionPull Λ f).map b)) ) ∧
  (∀ P Q H : CochainComplex (modules Λ Y) ℤ,
    TotalMapAgreement Λ X
      ((totalSectionPull Λ f).map (α_ P Q H).hom ≫
        (sectionTotalIso Λ f P (Q ⊗ H)).hom ≫
        (totalSectionPull Λ f).obj P ◁ (sectionTotalIso Λ f Q H).hom)
      ((sectionTotalIso Λ f (P ⊗ Q) H).hom ≫
        (sectionTotalIso Λ f P Q).hom ▷ (totalSectionPull Λ f).obj H ≫
        (α_ ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q)
          ((totalSectionPull Λ f).obj H)).hom) ) ∧
  (∀ P : CochainComplex (modules Λ Y) ℤ,
    TotalMapAgreement Λ X
      ((sectionTotalIso Λ f (𝟙_ (CochainComplex (modules Λ Y) ℤ)) P).hom ≫
        sectionTotalUnit Λ f ▷ (totalSectionPull Λ f).obj P ≫
        (λ_ ((totalSectionPull Λ f).obj P)).hom)
      ((totalSectionPull Λ f).map (λ_ P).hom) ) ∧
  (∀ P : CochainComplex (modules Λ Y) ℤ,
    TotalMapAgreement Λ X
      ((sectionTotalIso Λ f P (𝟙_ (CochainComplex (modules Λ Y) ℤ))).hom ≫
        (totalSectionPull Λ f).obj P ◁ sectionTotalUnit Λ f ≫
        (ρ_ ((totalSectionPull Λ f).obj P)).hom)
      ((totalSectionPull Λ f).map (ρ_ P).hom)
)

```

## Users

`tools/downstream.py Sheaf.Paper.SectionOplaxTotalComparison --names` lists 37 transitive importers. The table includes each one. The modification preserves the complete original data by definitional equality, so every consumer retains its meaning. No held module is adapted. Targets using these definitions are reopened for the independent statement review; the report records the Lean preservation checks.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SectionOplaxTotalComparison` | D8 | Implementation changed; whole-construction preservation checked separately. |
| `Sheaf.AlgebraicGeometry.FieldScalarProjectionMateCoherence` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.CanonicalCoefficientTensorNormalization` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.CountableNormProjectionCriterion` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.FilteredFlatTensorCohomology` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.FlatScalarGeometricCoherence` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.FlatScalarUnitNormalization` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.IntegralReductionUnderlyingDirectImage` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalCanonicalTensorPullRouteModel` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarMateProjection` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarProjectionMate` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarPullRouteModel` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarPullTensorCounit` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarPullbackNormalization` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarRegularPullCounit` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarTensorPullNormalization` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalTensorPullRouteModel` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.NormalizedScalarRestrictionPush` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.NormalizedScalarSectionFamily` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.RestrictedCoefficientPullbackData` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.ScalarChangeDirectImageUnit` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.ScalarGeometricExchangeRectangle` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionDerivedRepresentativeSquare` | U3 | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionDerivedTensorNormalization` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolutionConjugationIdentities` | G6 | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolvingOplaxConstraintData` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolvingOplaxConstraintDiagrams` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolvingOplaxInternalConjugation` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolvingOplaxModelEdges` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolvingOplaxUnitModels` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionScalarComputationTransport` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionTensorConjugateComputation` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionTensorNormalizationTransport` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionTensorRightComputation` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionCone` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionTower` | unclaimed | Same data and statements by definitional equality; no adaptation. |

## Status

landed 20261026T102357-L-347171 2026-10-26 (merge of deliver/D8/Sheaf.Paper.SectionOplaxTotalComparison)
