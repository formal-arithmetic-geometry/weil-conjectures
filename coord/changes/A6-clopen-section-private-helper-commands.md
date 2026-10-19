# AlgebraicGeometry.Scheme.clopenSectionComponent

## Reason

The completed proof adds generic private helper sections with a second universe `v`,
section variables for three preadditive categories, and a local instance attribute for
`preservesBinaryBiproduct_of_preservesBiproduct`. The static interface gate requires
this record for those commands. Both `Generic` sections end before the scheme-specific
helpers. The local attribute is scoped to the existing namespace. All new declarations
are private, all proofs are complete, and no private name occurs in a public signature
or public definition body.

The public theorem signature and all three original definitions are verbatim unchanged.
All original public imports remain. Only proof imports change, as listed in report.md.
No consumer statement, including any target, changes meaning. No consumer needs adaptation.
The two direct importers are `Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint` and
`Sheaf.Paper.RefinementCoefficientMate`; neither refers to the four public declaration
names in its source. The full transitive consumer inventory is below.

## Old

```lean
theorem clopenSectionComponent {X V : Scheme.{u}} (q : V ⟶ X) (s : X ⟶ V)
    [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base))
    (hsection : s ≫ q = 𝟙 X) (A : Type u) [CommRing A] [Finite A] :
    ((Functor.prod'
        (sfIntrinsicOpenRestriction s A)
        (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)).IsEquivalence ∧
      PreservesFiniteLimits
        (Functor.prod'
          (sfIntrinsicOpenRestriction s A)
          (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)) ∧
      PreservesFiniteColimits
        (Functor.prod'
          (sfIntrinsicOpenRestriction s A)
          (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A))) ∧
      (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)),
        Nonempty
          ((Functor.prod'
              (sfIntrinsicOpenRestriction s A)
              (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)).obj
            ((sfIntrinsicExtensionByZero s A).obj M) ≅
            ((M, 0) :
              proEtaleRingModules X (proEtaleConstantRing X A) ×
                proEtaleRingModules (clopenComplement s hclosed).toScheme
                  (proEtaleConstantRing (clopenComplement s hclosed).toScheme A)))) ∧
      (Functor.prod'
        ((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ))
        ((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
          (.up ℤ))).IsEquivalence ∧
      (∀ (K : CochainComplex
          (proEtaleRingModules V (proEtaleConstantRing V A)) ℤ),
        HomologicalComplex.Acyclic K ↔
          (HomologicalComplex.Acyclic
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).obj K) ∧
            HomologicalComplex.Acyclic
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).obj K))) ∧
      (∀ {E F : CochainComplex
          (proEtaleRingModules V (proEtaleConstantRing V A)) ℤ} (f g : E ⟶ F),
        Nonempty (Homotopy f g) ↔
          (Nonempty (Homotopy
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).map f)
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).map g)) ∧
            Nonempty (Homotopy
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).map f)
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).map g)))) ∧
      (∀ (I : CochainComplex
          (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
        CochainComplex.IsKInjective I →
          CochainComplex.IsKInjective
            (((sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ)).obj I)) ∧
      (∃ e : sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A ≅
          𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)),
        ClopenSectionComparisonOnSections q s hsection A e.hom ∧
        ∃ eC : (sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ) ⋙
            (proEtaleConstantModuleDirectImage q A).mapHomologicalComplex (.up ℤ) ≅
          𝟭 (CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
          (∀ (K : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ) (n : ℤ),
            (eC.hom.app K).f n = e.hom.app (K.X n)) ∧
          (∀ {E F : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ} (f : E ⟶ F),
            ((sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ) ⋙
                (proEtaleConstantModuleDirectImage q A).mapHomologicalComplex (.up ℤ)).map f ≫
              eC.hom.app F = eC.hom.app E ≫ f) ∧
          (∀ {E F : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ}
              {f g : E ⟶ F} (h : Homotopy f g) (i j : ℤ),
            (sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A).map
                (h.hom i j) ≫ e.hom.app (F.X j) =
              e.hom.app (E.X i) ≫ h.hom i j))
```

There are no generic helper sections or local biproduct-preservation instance attribute.

## New

```lean
theorem clopenSectionComponent {X V : Scheme.{u}} (q : V ⟶ X) (s : X ⟶ V)
    [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base))
    (hsection : s ≫ q = 𝟙 X) (A : Type u) [CommRing A] [Finite A] :
    ((Functor.prod'
        (sfIntrinsicOpenRestriction s A)
        (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)).IsEquivalence ∧
      PreservesFiniteLimits
        (Functor.prod'
          (sfIntrinsicOpenRestriction s A)
          (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)) ∧
      PreservesFiniteColimits
        (Functor.prod'
          (sfIntrinsicOpenRestriction s A)
          (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A))) ∧
      (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)),
        Nonempty
          ((Functor.prod'
              (sfIntrinsicOpenRestriction s A)
              (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)).obj
            ((sfIntrinsicExtensionByZero s A).obj M) ≅
            ((M, 0) :
              proEtaleRingModules X (proEtaleConstantRing X A) ×
                proEtaleRingModules (clopenComplement s hclosed).toScheme
                  (proEtaleConstantRing (clopenComplement s hclosed).toScheme A)))) ∧
      (Functor.prod'
        ((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ))
        ((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
          (.up ℤ))).IsEquivalence ∧
      (∀ (K : CochainComplex
          (proEtaleRingModules V (proEtaleConstantRing V A)) ℤ),
        HomologicalComplex.Acyclic K ↔
          (HomologicalComplex.Acyclic
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).obj K) ∧
            HomologicalComplex.Acyclic
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).obj K))) ∧
      (∀ {E F : CochainComplex
          (proEtaleRingModules V (proEtaleConstantRing V A)) ℤ} (f g : E ⟶ F),
        Nonempty (Homotopy f g) ↔
          (Nonempty (Homotopy
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).map f)
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).map g)) ∧
            Nonempty (Homotopy
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).map f)
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).map g)))) ∧
      (∀ (I : CochainComplex
          (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
        CochainComplex.IsKInjective I →
          CochainComplex.IsKInjective
            (((sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ)).obj I)) ∧
      (∃ e : sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A ≅
          𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)),
        ClopenSectionComparisonOnSections q s hsection A e.hom ∧
        ∃ eC : (sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ) ⋙
            (proEtaleConstantModuleDirectImage q A).mapHomologicalComplex (.up ℤ) ≅
          𝟭 (CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
          (∀ (K : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ) (n : ℤ),
            (eC.hom.app K).f n = e.hom.app (K.X n)) ∧
          (∀ {E F : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ} (f : E ⟶ F),
            ((sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ) ⋙
                (proEtaleConstantModuleDirectImage q A).mapHomologicalComplex (.up ℤ)).map f ≫
              eC.hom.app F = eC.hom.app E ≫ f) ∧
          (∀ {E F : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ}
              {f g : E ⟶ F} (h : Homotopy f g) (i j : ℤ),
            (sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A).map
                (h.hom i j) ≫ e.hom.app (F.X j) =
              e.hom.app (E.X i) ≫ h.hom i j))
```

The added scoped implementation commands are:

```lean
attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct
section Generic
universe v
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasBinaryBiproducts C]
-- private pair_equivalence
end Generic
section Generic
universe v
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [Preadditive C] [Preadditive D] [Preadditive E]
-- private pair_homotopy and pair_complex_equivalence
end Generic
```

## Users

Inventory from `tools/downstream.py` on the shared sources. The textual `--uses`
checks for `clopenSectionComponent`, `clopenComplement`, `clopenSectionComponentArrow`
and `ClopenSectionComparisonOnSections` find only the assigned module itself.
Consumer imports continue to expose exactly the original public declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClopenSectionComponent | A6 | Private proof helpers; same public signature and definitions |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.RefinementCoefficientMate | X6 | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.SfBidualityClass | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Unchanged signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Unchanged signatures and definitions; no adaptation |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged signatures and definitions; no adaptation |
| TargetsCheck | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.Statement | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged signatures and definitions; no adaptation |

## Status

landed 20261019T112435-L-3939625 2026-10-19 (merge of deliver/A6/Sheaf.AlgebraicGeometry.ClopenSectionComponent)
