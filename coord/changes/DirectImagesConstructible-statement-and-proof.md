# WeilConjectures.directImages_constructible

## Reason

The final two common-stage clauses used `HEq M.obj.obj` with an ambient derived
object on the right. The left side is an integral constructible object, one
structure layer above the intended derived object. The repair projects it once
more, to `M.obj.obj.obj`. This restores the intended underlying-object equality
in the unchanged natural-language DAG statement. No definition or target
signature changes. The other clauses, binders and universes are unchanged.

Both original holes are proved: the unit assertion from finite-field
characteristic, and the repaired direct-image statement from fixed etale origin,
finite-type finiteness, comparison, the finite compact-support theorem, the
integral direct-image theorem, and the stored integral compact-support property.
There are no new declarations or holes.

## Old

```lean
theorem directImages_constructible
    (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (E₀ : Padic.FiniteCoefficientFields l Ω)
    (n : ℕ) (hn : 1 ≤ n)
    (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    {Kₙ : proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)}
    (hKₙ : intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀)
      n hn Y Kₙ)
    {K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E₀) Y}
    (L : @SfIntegralDirectImage l inferInstance (Coefficient.{u} l Ω E₀)
      inferInstance inferInstance inferInstance
      Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
        let : HasCountableProducts
            (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
              (Spec (CommRingCat.of D.k)))) :=
          integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
            (Spec (CommRingCat.of D.k))
        infer_instance))
    : intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
          (Spec (CommRingCat.of D.k))
          ((proEtaleConstantDerivedDirectImage (Y ↘ Spec (CommRingCat.of D.k))
            (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)).obj Kₙ) ∧
      intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
          (Spec (CommRingCat.of D.k))
          ((@AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport Y (Spec (CommRingCat.of D.k))
            (Y ↘ Spec (CommRingCat.of D.k)) c
            (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n) _
            (Padic.finite_coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n hn)).obj Kₙ) ∧
      sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k))
        (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k))
        (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k (by
          exact finiteFieldDatumPrimeUnit D l hl) c K).obj ∧
      ∃ M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k)),
        M.obj.obj = (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      ∃ M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k)),
        M.obj.obj = (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
          (finiteFieldDatumPrimeUnit D l hl) c K).obj ∧
      ∃ M : generalAlgebraicallyClosedConstructibleCategory l Ω
          (Spec (CommRingCat.of D.k)),
        M.stage = E₀ ∧ HEq M.obj.obj
          (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      ∃ M : generalAlgebraicallyClosedConstructibleCategory l Ω
          (Spec (CommRingCat.of D.k)),
        M.stage = E₀ ∧ HEq M.obj.obj
          ((sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
            (finiteFieldDatumPrimeUnit D l hl) c K).obj)
```

## New

```lean
theorem directImages_constructible
    (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (E₀ : Padic.FiniteCoefficientFields l Ω)
    (n : ℕ) (hn : 1 ≤ n)
    (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    {Kₙ : proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)}
    (hKₙ : intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀)
      n hn Y Kₙ)
    {K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E₀) Y}
    (L : @SfIntegralDirectImage l inferInstance (Coefficient.{u} l Ω E₀)
      inferInstance inferInstance inferInstance
      Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
        let : HasCountableProducts
            (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
              (Spec (CommRingCat.of D.k)))) :=
          integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
            (Spec (CommRingCat.of D.k))
        infer_instance))
    : intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
          (Spec (CommRingCat.of D.k))
          ((proEtaleConstantDerivedDirectImage (Y ↘ Spec (CommRingCat.of D.k))
            (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)).obj Kₙ) ∧
      intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
          (Spec (CommRingCat.of D.k))
          ((@AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport Y (Spec (CommRingCat.of D.k))
            (Y ↘ Spec (CommRingCat.of D.k)) c
            (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n) _
            (Padic.finite_coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n hn)).obj Kₙ) ∧
      sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k))
        (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k))
        (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k (by
          exact finiteFieldDatumPrimeUnit D l hl) c K).obj ∧
      ∃ M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k)),
        M.obj.obj = (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      ∃ M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k)),
        M.obj.obj = (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
          (finiteFieldDatumPrimeUnit D l hl) c K).obj ∧
      ∃ M : generalAlgebraicallyClosedConstructibleCategory l Ω
          (Spec (CommRingCat.of D.k)),
        M.stage = E₀ ∧ HEq M.obj.obj.obj
          (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      ∃ M : generalAlgebraicallyClosedConstructibleCategory l Ω
          (Spec (CommRingCat.of D.k)),
        M.stage = E₀ ∧ HEq M.obj.obj.obj
          ((sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
            (finiteFieldDatumPrimeUnit D l hl) c K).obj)
```

## Users

`tools/downstream.py Sheaf.Paper.DirectImagesConstructible --uses
WeilConjectures.directImages_constructible` found only the changed module and
`Sheaf.Paper.OrdinaryCompactCohomology` as name users. The latter's only
application extracts clauses one and two, whose types are unchanged; its
original source compiled against the repaired module (31.3 seconds). No
consumer adaptation is delivered. All transitive import consumers are listed
below; none refers to either changed common-stage clause. Holders are from the
claim records at record generation. The unchanged finiteFieldDatumPrimeUnit
signature is proved, so its uses have the identical proposition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DirectImagesConstructible | G1 | Repairs two common-stage projections and proves both declarations. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | P9 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | F9 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.AdicSectionClosedSupport | Y5 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.AdmissibleVerdierExchange | R1 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | N1 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CompactSupportPerfectness | Q4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CompactSupportProjectionFormula | A4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | Y9 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CompletedTensorHomTranspose | D2 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ConnectedConstantH0 | W3 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | J4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Q1 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | N3 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | Y6 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | X3 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | A5 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | D9 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.GlobalVerdierDuality | R5 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.InternalHomPullback | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.IteratedWeilCocycle | D4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | A6 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.LocalizedTopChern | E5 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.MiddleExtensionHcZero | E5 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Uses only unchanged first two clauses; compiled original unchanged. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.PointCompletedEvaluation | T8 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | E3 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | G4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ProperCoincidenceFrobenius | H6 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ProperCompactCoincidence | P9 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ProperProductCounitTranspose | N4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | K7 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.RationalStalkExact | A7 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TrfDevissageGeneration | C2 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TrfWitnessedOpenPullback | J8 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TwConventions | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | S2 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.WfTensorCompletionFrobenius | U8 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A6 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Q8 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | T8 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | P4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | H6 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.FiniteExceptional | K1 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | M7 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | B5 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | M2 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.IntegralDualizing | G8 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | R6 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.RationalVerdier | V4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | E4 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | Y7 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | T2 | No application of the changed theorem; definitions and other interfaces unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| TargetsCheck | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.Statement | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No application of the changed theorem; definitions and other interfaces unchanged. |

## Status

landed 20261020T051305-L-1622630 2026-10-20 (merge of deliver/G1/Sheaf.Paper.DirectImagesConstructible)

Main module compiled in 18.2 seconds after pruning. Its direct consumer compiled
unchanged in the same sandbox. No target definition or target signature changed,
so no target semantic review is reopened by this intermediate projection repair.
The mathematical node statement is unchanged; its `lean.statement`, `proof`,
`proof_deps` and `proof_origin` record the repaired Lean signature and actual proof.
