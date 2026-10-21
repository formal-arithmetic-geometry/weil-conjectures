# WeilConjectures.sfDerivedRestrictionComparison_existsUnique

## Reason

Specify the existing source and target of the complex map `j` explicitly in the displayed
normalization. With these arguments implicit, Lean tries to reconstruct the restriction
functor's object from the map, repeatedly unfolding sheafification and completed coefficient
limits. This annotation avoids that inference problem. The old and new terms have exactly
the same elaborated mathematical type: no binder, hypothesis, universe, conclusion or
coefficient construction changes. The preflight's syntactic statement comparison requests
this record. This declaration is not one of the five target statements.

The local irreducibility attributes added only for proof checking are scoped to this module;
no public definition body or imported source module is changed. The node's mathematical
statement stays unchanged. No target's meaning changes and no semantic target review is
reopened.

## Old

```lean
theorem sfDerivedRestrictionComparison_existsUnique (n : ℕ) :
    ∃! e : scalarReductionDerivedRestriction.{u, u} l E X n ⋙
          sfCompletedDerivedDirectImage l E f ≅
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
          scalarReductionDerivedRestriction.{u, u} l E Y n,
      ∀ (J : CochainComplex (scalarReductionTarget.{u, u} l E X n) ℤ) [J.IsKInjective]
        (I : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ) [I.IsKInjective]
        (j : ((scalarReductionRestriction.{u, u} l E X n).mapHomologicalComplex (.up ℤ)).obj
          J ⟶ I) [QuasiIso j],
        e.hom.app (DerivedCategory.Q.obj J) ≫
            (scalarReductionDerivedRestriction.{u, u} l E Y n).map
              ((proEtaleConstantModuleDirectImage f
                (Padic.coefficientExtensionRing l E (n + 1))).rightDerivedFunctorObjQIso J).hom ≫
            (scalarReductionRestriction.{u, u} l E Y n).mapDerivedCategoryFactors.hom.app
              (((proEtaleConstantModuleDirectImage f
                (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
                  (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (sfDirectImageRestrictionComparison l E f n) (.up ℤ)).hom.app J) ≫
            DerivedCategory.Q.map
              (((sfCompletedModuleDirectImage l E f).mapHomologicalComplex (.up ℤ)).map j) =
          (sfCompletedDerivedDirectImage l E f).map
              ((scalarReductionRestriction.{u, u} l E X n).mapDerivedCategoryFactors.hom.app J) ≫
            (sfCompletedDerivedDirectImage l E f).map (DerivedCategory.Q.map j) ≫
            ((sfCompletedModuleDirectImage l E f).rightDerivedFunctorObjQIso I).hom
```

## New

```lean
theorem sfDerivedRestrictionComparison_existsUnique (n : ℕ) :
    ∃! e : scalarReductionDerivedRestriction.{u, u} l E X n ⋙
          sfCompletedDerivedDirectImage l E f ≅
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
          scalarReductionDerivedRestriction.{u, u} l E Y n,
      ∀ (J : CochainComplex (scalarReductionTarget.{u, u} l E X n) ℤ) [J.IsKInjective]
        (I : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ) [I.IsKInjective]
        (j : ((scalarReductionRestriction.{u, u} l E X n).mapHomologicalComplex (.up ℤ)).obj
          J ⟶ I) [QuasiIso j],
        e.hom.app (DerivedCategory.Q.obj J) ≫
            (scalarReductionDerivedRestriction.{u, u} l E Y n).map
              ((proEtaleConstantModuleDirectImage f
                (Padic.coefficientExtensionRing l E (n + 1))).rightDerivedFunctorObjQIso J).hom ≫
            (scalarReductionRestriction.{u, u} l E Y n).mapDerivedCategoryFactors.hom.app
              (((proEtaleConstantModuleDirectImage f
                (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
                  (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (sfDirectImageRestrictionComparison l E f n) (.up ℤ)).hom.app J) ≫
            DerivedCategory.Q.map
              (((sfCompletedModuleDirectImage l E f).mapHomologicalComplex (.up ℤ)).map
                (X := ((scalarReductionRestriction.{u, u} l E X n).mapHomologicalComplex
                  (.up ℤ)).obj J) (Y := I) j) =
          (sfCompletedDerivedDirectImage l E f).map
              ((scalarReductionRestriction.{u, u} l E X n).mapDerivedCategoryFactors.hom.app J) ≫
            (sfCompletedDerivedDirectImage l E f).map (DerivedCategory.Q.map j) ≫
            ((sfCompletedModuleDirectImage l E f).rightDerivedFunctorObjQIso I).hom
```

## Users

`tools/downstream.py Sheaf.Paper.SfDerivedDirectImage --uses sfDerivedRestrictionComparison_existsUnique` finds only the item module
as a textual user of this declaration (the declaration and its chosen-comparison definition).
The table also includes every transitive importer returned by that command. None requires
adaptation: the annotation fills the same implicit arguments that the old statement already
inferred. Existing statements remain neither stronger nor weaker. The unchanged definitions
expose the same interface to all these modules. Claim holders are the current coordination
records at preparation time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfDerivedDirectImage | F4 | Own module: chosen comparison consumes the theorem with the same type; compiled. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization | X2 | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedComponentInverseImage | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | C1 | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedProfiniteScalarCompatibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization | S2 | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleEvaluationAdjunction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ExceptionalBaseChangeReducesToProper | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentCoefficientComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | C3 | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | R6 | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenModuleRestrictionIdentities | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage | F3 | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.SfFullcdUsedClass | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.FieldTheory.CondensedSubfieldBasis | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.NumberTheory.Padics.BaseCoefficientCondensedIdentification | S6 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | E2 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ClosedSupportBoundedContinuity | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CoefficientProjectionSquare | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CohomologyTorInterval | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | P3 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CompletedPullbackTensorComparison | C5 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | A3 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedCompactSupportProjection | T2 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedERealization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | S2 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | C6 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstantWeilStructure | H9 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | C8 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleTruncations | C9 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | J5 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DerivedExchangeExactNormalization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DerivedNakayama | D5 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorIso | J6 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | D7 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ExceptionalSupportProjectionIso | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | J7 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteCoefficientModelComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | E6 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | J8 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | E7 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | E8 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | G4 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | F4 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | E2 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingCompactification | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingConstructibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingNaturality | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingTensorTor | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEncoding | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteExtensionReductionConeBound | E9 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | B5 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteProjectionActionLaws | J9 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralCoherenceTower | S3 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | W4 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralCriterionReductions | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralDerivedCoefficientData | D4 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | K6 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | F7 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | F8 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.InternalHomDualTorAmplitude | Q4 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | K7 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | A8 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | K8 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ModuleDerivedCompositorCoherence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PrincipalReductionConeCalculus | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | M6 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | M7 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.RealizationScalarFunctor | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ResidueLisseProjectiveModels | P5 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | P6 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SectionDerivedRealization | T1 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SectionOrdinaryOplaxNormalization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SfCompactSupportRestrictionOfScalars | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | Q7 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | Q8 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.StratifiedLattice | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SupportScalarProjectionNormalization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | G7 | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | G8 | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | G9 | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | H5 | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | V3 | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | B2 | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.SixFunctors.ScalarSixPullback | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.Topology.ProfiniteSectionsFiniteQuotient | U3 | Unchanged type and definitions; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | H6 | Unchanged type and definitions; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Unchanged type and definitions; no adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Unchanged type and definitions; no adaptation. |
| TargetsCheck | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Homology | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Unchanged type and definitions; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Unchanged type and definitions; no adaptation. |

## Status

landed 20261021T101005-L-4184293 2026-10-21 (merge of deliver/F4/Sheaf.Paper.SfDerivedDirectImage)
