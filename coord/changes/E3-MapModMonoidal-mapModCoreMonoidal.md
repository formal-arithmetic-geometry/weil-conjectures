# CategoryTheory.Functor.mapModCoreMonoidal

## Reason

Complete the five coherence proofs in the existing `Functor.CoreMonoidal` construction.
The delivery tool conservatively classifies an edited definition body as an interface change,
so this record documents the unchanged data and the downstream effect. The type, `εIso`,
and `μIso` are verbatim unchanged. All changed fields are propositions: tensor naturality,
associativity, and the two unit axioms. Proof irrelevance therefore preserves the definition
up to equality and preserves every downstream mathematical statement. No target statement
or definition of a target's mathematical data changes.

## Old

```lean
noncomputable def mapModCoreMonoidal : (F.mapMod R).CoreMonoidal where
  εIso := F.mapModUnitIso
  μIso := F.mapModTensorIso
  μIso_hom_natural_left := sorry
  μIso_hom_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry
```

## New

```lean
noncomputable def mapModCoreMonoidal : (F.mapMod R).CoreMonoidal where
  εIso := F.mapModUnitIso
  μIso := F.mapModTensorIso
  μIso_hom_natural_left := by
    intro M N f P
    ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj P))]
    simp only [Mod.comp_hom', Mod.tensorObjπ_whiskerRight_assoc,
      tensorπ_mapModTensorIso_hom_hom_assoc]
    change F.map f.hom ▷ F.obj P.X ≫
        (Mod.tensorObjπ ((F.mapMod R).obj N) ((F.mapMod R).obj P) ≫
          (F.mapModTensorIso N P).hom.hom) =
      LaxMonoidal.μ F M.X P.X ≫ F.map (Mod.tensorObjπ M P) ≫ F.map (f ▷ P).hom
    rw [tensorπ_mapModTensorIso_hom_hom, LaxMonoidal.μ_natural_left_assoc,
      ← F.map_comp, ← F.map_comp, Mod.tensorObjπ_whiskerRight]
  μIso_hom_natural_right := by
    intro M N P f
    ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj P) ((F.mapMod R).obj M))]
    simp only [Mod.comp_hom', Mod.tensorObjπ_whiskerLeft_assoc,
      tensorπ_mapModTensorIso_hom_hom_assoc]
    change F.obj P.X ◁ F.map f.hom ≫
        (Mod.tensorObjπ ((F.mapMod R).obj P) ((F.mapMod R).obj N) ≫
          (F.mapModTensorIso P N).hom.hom) =
      LaxMonoidal.μ F P.X M.X ≫ F.map (Mod.tensorObjπ P M) ≫ F.map (P ◁ f).hom
    rw [tensorπ_mapModTensorIso_hom_hom, LaxMonoidal.μ_natural_right_assoc,
      ← F.map_comp, ← F.map_comp, Mod.tensorObjπ_whiskerLeft]
  associativity := by
    intro M N P
    ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N) ▷
      ((F.mapMod R).obj P).X ≫
        Mod.tensorObjπ (((F.mapMod R).obj M) ⊗ ((F.mapMod R).obj N))
          ((F.mapMod R).obj P))]
    simp only [Mod.comp_hom', Category.assoc, Mod.tensorObjπ_whiskerRight_assoc]
    erw [← comp_whiskerRight_assoc, tensorπ_mapModTensorIso_hom_hom,
      comp_whiskerRight_assoc, tensorπ_mapModTensorIso_hom_hom_assoc]
    change LaxMonoidal.μ F M.X N.X ▷ F.obj P.X ≫
        F.map (Mod.tensorObjπ M N) ▷ F.obj P.X ≫
          LaxMonoidal.μ F (M ⊗ N).X P.X ≫ F.map (Mod.tensorObjπ (M ⊗ N) P) ≫
            F.map (α_ M N P).hom.hom = _
    rw [LaxMonoidal.μ_natural_left_assoc]
    simp only [← F.map_comp]
    rw [Mod.tensorObjπ_associator_hom]
    simp only [F.map_comp]
    rw [LaxMonoidal.associativity_assoc]
    erw [Mod.tensorObjπ_associator_hom_assoc, Mod.tensorObjπ_whiskerLeft_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, tensorπ_mapModTensorIso_hom_hom,
      MonoidalCategory.whiskerLeft_comp_assoc, tensorπ_mapModTensorIso_hom_hom]
    change _ = (α_ (F.obj M.X) (F.obj N.X) (F.obj P.X)).hom ≫
      F.obj M.X ◁ LaxMonoidal.μ F N.X P.X ≫ F.obj M.X ◁ F.map (Mod.tensorObjπ N P) ≫
        LaxMonoidal.μ F M.X (N ⊗ P).X ≫ F.map (Mod.tensorObjπ M (N ⊗ P))
    rw [LaxMonoidal.μ_natural_right_assoc]
  left_unitality := by
    intro M
    ext
    rw [← cancel_epi (Mod.tensorObjπ (𝟙_ (Mod D (F.obj R))) ((F.mapMod R).obj M))]
    simp only [Mod.comp_hom', Mod.tensorObjπ_whiskerRight_assoc]
    erw [Mod.tensorObjπ_leftUnitor_hom, tensorπ_mapModTensorIso_hom_hom_assoc]
    change LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X] =
      (𝟙 (F.obj R)) ▷ F.obj M.X ≫ LaxMonoidal.μ F R M.X ≫
        F.map (Mod.tensorObjπ (𝟙_ (Mod C R)) M) ≫ F.map (λ_ M).hom.hom
    rw [id_whiskerRight, Category.id_comp, ← F.map_comp, Mod.tensorObjπ_leftUnitor_hom]
  right_unitality := by
    intro M
    ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) (𝟙_ (Mod D (F.obj R))))]
    simp only [Mod.comp_hom', Mod.tensorObjπ_whiskerLeft_assoc]
    erw [Mod.tensorObjπ_rightUnitor_hom, tensorπ_mapModTensorIso_hom_hom_assoc]
    change (β_ (F.obj M.X) (F.obj R)).hom ≫
        LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X] =
      F.obj M.X ◁ (𝟙 (F.obj R)) ≫ LaxMonoidal.μ F M.X R ≫
        F.map (Mod.tensorObjπ M (𝟙_ (Mod C R))) ≫ F.map (ρ_ M).hom.hom
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, ← F.map_comp,
      Mod.tensorObjπ_rightUnitor_hom, F.map_comp, Functor.LaxBraided.braided_assoc]
```

## Users

The table includes every transitive downstream module reported by `tools/downstream.py`,
plus the item itself. The only downstream textual mention of either constructor is in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence` (for
`comapCoreMonoidal`); its unchanged proof uses the unit comparison, whose data is identical.
A single-file check of this unchanged consumer could not start because the shared compiled
library lacks its existing dependency `UpperLowerStar.Coherence.olean`; this is recorded
in the report, and no replacement of that dependency is introduced.
The remainder use the existing monoidal instances transitively, with identical tensorators,
unit maps, functors, hypotheses, and conclusions. There are no consumer adaptations.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal | E3 | Five coherence holes closed; all comparison data preserved. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | B2 | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | E1 | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | E4 | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | F1 | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | B3 | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | F2 | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| TargetsCheck | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | A4 | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal | D4 | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | G2 | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | G1 | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.TraceFormula.Main | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Same signature and comparison data; only proof fields completed; no adaptation. |

## Status

landed 20261016T221608-L-1614192 2026-10-16 (merge of deliver/E3/WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal)
