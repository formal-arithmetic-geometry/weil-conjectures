# Integral dualizing model interface

## Reason

Move the existing definitions and instances to `Sheaf.SixFunctors.IntegralDualizingRoosModel`, publicly reexported by the original module. This allows the independent finite-bounds and mapping-limit subarguments to refer to the same prescribed objects without an import cycle. Every existing declaration has its original name, signature, visibility, and body. The original public imports are preserved. No target statement or definition changes meaning.

## Old

In `Sheaf.SixFunctors.IntegralDualizing`, following the existing coefficient variables:

```lean
/-- The published sheafification instance with both universes specified.
Source: blueprint order 1455, ordinary coefficient sheaves
(blueprint: prop-coef-integral-dualizing). -/
instance integralDualizingRingSheafify (Y : Scheme.{u}) :
    HasSheafify (ProEt.topology Y) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} Y

/-- The coefficient ring in the section universe, with only a carrier lift.
Source: blueprint order 2145, D(R) (blueprint: prop-coef-integral-dualizing). -/
abbrev integralDualizingCoefficients := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- The actual constant scalar map to sections of the completion.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingScalar (Y : Scheme.{u}) (U : Y.ProEtᵒᵖ) :
    integralDualizingCoefficients l E →+*
      (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U :=
  (((integralConstantToCompletionOfUniverses.{u, u} l E Y).hom.app U).hom).comp
    (((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((toSheafify (D := CommRingCat.{u + 1}) (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj
          (CommRingCat.of (integralDualizingCoefficients l E)))).app U)).hom)

/-- Ordinary global sections with their actual R action, evaluated at the final object.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingSections (Y : Scheme.{u}) :
    scalarReductionSource l E Y ⥤ ModuleCat.{u + 1} (integralDualizingCoefficients l E) :=
  SheafOfModules.evaluation _ (op (ProEt.mk (𝟙 Y))) ⋙
    ModuleCat.restrictScalars (integralDualizingScalar l E Y (op (ProEt.mk (𝟙 Y))))

/-- Evaluation and scalar restriction are additive, with the existing module structures.
Source: blueprint order 2145 (blueprint: prop-coef-integral-dualizing). -/
instance integralDualizingSections_additive (Y : Scheme.{u}) :
    (integralDualizingSections l E Y).Additive :=
  inferInstanceAs (SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op (ProEt.mk (𝟙 Y))) ⋙
    ModuleCat.restrictScalars (integralDualizingScalar l E Y (op (ProEt.mk (𝟙 Y))))).Additive

/-- Derived sections computed on the published K-injective replacements.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingDerivedSections (Y : Scheme.{u}) :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
    (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y)).1
  (integralDualizingSections l E Y).rightDerivedFunctor

/-- Global derived Hom is RΓ of the recorded internal derived Hom.
Source: blueprint order 2145, definition of RHom_X
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingGlobalHom (Y : Scheme.{u})
    (M : DerivedCategory (scalarReductionSource l E Y)) :
    (sfIntegralConstructibleCategory l E Y)ᵒᵖ ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (sfIntegralConstructible l E Y).ι.op ⋙
    (Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
      (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y))).flip.obj M ⋙
      integralDualizingDerivedSections l E Y

/-- Total right derived inverse limit on strict completed-coefficient towers.
The chosen functor has the right-derived universal property, so is unique up to the
unique comparison compatible with its derived unit. Its data is not an arbitrary cone.
Source: blueprint order 2145 and Stacks 0940--0941
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingLimit (Y : Scheme.{u}) :
    DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  (ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
    (ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
    (completedIntegralCoefficient_mul_commUnrestricted l E Y)).choose

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The compactification supplied by Nagata over the given field.
Source: blueprint order 2145, a:X→s (blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactification : Compactification (X ↘ Spec (.of D.k)) :=
  letI := hasCompactification_of_finiteType_over_field D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k))
  HasCompactification.compactification (X ↘ Spec (.of D.k))

/-- The published coherent compact-support reduction functor, including all transitions
and all derived morphisms. Its evaluation and transition characterizations determine its
coherent tower up to isomorphism. Only normalized scalar structures from that construction
are used to extract the functor.
Source: blueprint order 2145 and Bhatt--Scholze 6.7.6
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactTower :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) := by
  let h := exists_compactSupportReductionTower l E D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k)) (finiteFieldDatumPrimeUnit D l hl)
      (integralDualizingCompactification D X)
  letI := h.choose
  letI := h.choose_spec.choose
  exact h.choose_spec.choose_spec.2.2.choose

/-- Integral compact support followed by coefficient-point sections, with its map action.
Source: blueprint order 2145, C=Γ(s,Ra_!K)
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactSections : sfIntegralConstructibleCategory l E X ⥤
    DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (sfIntegralConstructible l E X).ι ⋙ integralDualizingCompactTower l E D hl X ⋙
    integralDualizingLimit l E (Spec (.of D.k)) ⋙
      integralDualizingDerivedSections l E (Spec (.of D.k))

/-- A Roos limit presentation of the coherent normalized tower, with the actual counit
reductions and their compatibility with every quotient transition. This is a predicate on
real objects and maps, using the published countable products and effectivity comparisons.
Source: blueprint order 2145, first display and transition paragraph
(blueprint: prop-coef-integral-dualizing). -/
def IntegralDualizingLimitPresentation (T : NormalizedDVRTower l E X D hl)
    (M : DerivedCategory (scalarReductionSource l E X)) : Prop :=
  letI : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  ∃ (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧),
    IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
        M p δ ∧
    (∀ n : ℕ, IsIso (normalizedDVRCounitComparison l E X D hl T M p n)) ∧
    ∀ (m n : ℕ) (h : n ≤ m),
      normalizedDVRCounitComparison l E X D hl T M p m ≫ T.tau h =
        normalizedDVRReductionTransition l E X D hl h M ≫
          (normalizedDVRRes l E X h).map
            (normalizedDVRCounitComparison l E X D hl T M p n)

```

## New

The identical block below is in `Sheaf.SixFunctors.IntegralDualizingRoosModel`, following identical coefficient variables. The original module has `public import Sheaf.SixFunctors.IntegralDualizingRoosModel`.

```lean
/-- The published sheafification instance with both universes specified.
Source: blueprint order 1455, ordinary coefficient sheaves
(blueprint: prop-coef-integral-dualizing). -/
instance integralDualizingRingSheafify (Y : Scheme.{u}) :
    HasSheafify (ProEt.topology Y) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} Y

/-- The coefficient ring in the section universe, with only a carrier lift.
Source: blueprint order 2145, D(R) (blueprint: prop-coef-integral-dualizing). -/
abbrev integralDualizingCoefficients := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- The actual constant scalar map to sections of the completion.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingScalar (Y : Scheme.{u}) (U : Y.ProEtᵒᵖ) :
    integralDualizingCoefficients l E →+*
      (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U :=
  (((integralConstantToCompletionOfUniverses.{u, u} l E Y).hom.app U).hom).comp
    (((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((toSheafify (D := CommRingCat.{u + 1}) (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj
          (CommRingCat.of (integralDualizingCoefficients l E)))).app U)).hom)

/-- Ordinary global sections with their actual R action, evaluated at the final object.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingSections (Y : Scheme.{u}) :
    scalarReductionSource l E Y ⥤ ModuleCat.{u + 1} (integralDualizingCoefficients l E) :=
  SheafOfModules.evaluation _ (op (ProEt.mk (𝟙 Y))) ⋙
    ModuleCat.restrictScalars (integralDualizingScalar l E Y (op (ProEt.mk (𝟙 Y))))

/-- Evaluation and scalar restriction are additive, with the existing module structures.
Source: blueprint order 2145 (blueprint: prop-coef-integral-dualizing). -/
instance integralDualizingSections_additive (Y : Scheme.{u}) :
    (integralDualizingSections l E Y).Additive :=
  inferInstanceAs (SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op (ProEt.mk (𝟙 Y))) ⋙
    ModuleCat.restrictScalars (integralDualizingScalar l E Y (op (ProEt.mk (𝟙 Y))))).Additive

/-- Derived sections computed on the published K-injective replacements.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingDerivedSections (Y : Scheme.{u}) :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
    (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y)).1
  (integralDualizingSections l E Y).rightDerivedFunctor

/-- Global derived Hom is RΓ of the recorded internal derived Hom.
Source: blueprint order 2145, definition of RHom_X
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingGlobalHom (Y : Scheme.{u})
    (M : DerivedCategory (scalarReductionSource l E Y)) :
    (sfIntegralConstructibleCategory l E Y)ᵒᵖ ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (sfIntegralConstructible l E Y).ι.op ⋙
    (Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
      (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y))).flip.obj M ⋙
      integralDualizingDerivedSections l E Y

/-- Total right derived inverse limit on strict completed-coefficient towers.
The chosen functor has the right-derived universal property, so is unique up to the
unique comparison compatible with its derived unit. Its data is not an arbitrary cone.
Source: blueprint order 2145 and Stacks 0940--0941
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingLimit (Y : Scheme.{u}) :
    DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  (ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
    (ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
    (completedIntegralCoefficient_mul_commUnrestricted l E Y)).choose

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The compactification supplied by Nagata over the given field.
Source: blueprint order 2145, a:X→s (blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactification : Compactification (X ↘ Spec (.of D.k)) :=
  letI := hasCompactification_of_finiteType_over_field D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k))
  HasCompactification.compactification (X ↘ Spec (.of D.k))

/-- The published coherent compact-support reduction functor, including all transitions
and all derived morphisms. Its evaluation and transition characterizations determine its
coherent tower up to isomorphism. Only normalized scalar structures from that construction
are used to extract the functor.
Source: blueprint order 2145 and Bhatt--Scholze 6.7.6
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactTower :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) := by
  let h := exists_compactSupportReductionTower l E D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k)) (finiteFieldDatumPrimeUnit D l hl)
      (integralDualizingCompactification D X)
  letI := h.choose
  letI := h.choose_spec.choose
  exact h.choose_spec.choose_spec.2.2.choose

/-- Integral compact support followed by coefficient-point sections, with its map action.
Source: blueprint order 2145, C=Γ(s,Ra_!K)
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactSections : sfIntegralConstructibleCategory l E X ⥤
    DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (sfIntegralConstructible l E X).ι ⋙ integralDualizingCompactTower l E D hl X ⋙
    integralDualizingLimit l E (Spec (.of D.k)) ⋙
      integralDualizingDerivedSections l E (Spec (.of D.k))

/-- A Roos limit presentation of the coherent normalized tower, with the actual counit
reductions and their compatibility with every quotient transition. This is a predicate on
real objects and maps, using the published countable products and effectivity comparisons.
Source: blueprint order 2145, first display and transition paragraph
(blueprint: prop-coef-integral-dualizing). -/
def IntegralDualizingLimitPresentation (T : NormalizedDVRTower l E X D hl)
    (M : DerivedCategory (scalarReductionSource l E X)) : Prop :=
  letI : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  ∃ (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧),
    IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
        M p δ ∧
    (∀ n : ℕ, IsIso (normalizedDVRCounitComparison l E X D hl T M p n)) ∧
    ∀ (m n : ℕ) (h : n ≤ m),
      normalizedDVRCounitComparison l E X D hl T M p m ≫ T.tau h =
        normalizedDVRReductionTransition l E X D hl h M ≫
          (normalizedDVRRes l E X h).map
            (normalizedDVRCounitComparison l E X D hl T M p n)

```

## Users

All downstream modules reported by `tools/downstream.py` are listed. None requires an adaptation because the same declarations and public prerequisites are reexported.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.IntegralDualizing | Z6 | Publicly reexports the identical definitions; complete assembly proof. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | T2 | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | B4 | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | D2 | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | B6 | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Identical reexported interface and mathematical meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingRoosModel | Z6, new | Owns the unchanged definitions and the strict tower subargument. |
| Sheaf.SixFunctors.IntegralDualizingFiniteBounds | Z6, new | Uses the same finite objects. |
| Sheaf.SixFunctors.IntegralDualizingMappingLimit | Z6, new | Uses the same sections and mapping functors. |

## Status

landed 20261025T124537-L-2065790 2026-10-25 (merge of deliver/Z6/Sheaf.SixFunctors.IntegralDualizing)
