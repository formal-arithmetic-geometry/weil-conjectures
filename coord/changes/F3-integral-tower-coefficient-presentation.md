# WeilConjectures.integralTowerModules

## Reason

The completed scalar-change witness uses modules over the ring sheaf obtained by forgetting
commutativity of completedIntegralCommRingSheafUnrestricted. The tower abbreviation used the
recorded completed ring sheaf instead. These ring sheaves are definitionally equal, but comparison
of their induced additive and derived structures repeatedly expands sheafification and causes the
completed scalar shift proof to exceed the per-file compile limit. Use the same presentation as
the existing universal scalar-change witness. This repairs an unclaimed Sheaf module.

This changes no mathematical data. The commutative presheaf has the recorded ring presheaf's
objects and maps and adds only its proved commutativity. Forgetting it recovers that ring
presheaf definitionally; the sheaf proof is irrelevant. Consequently the old and new category
abbreviations, their standard derived localizations, and every statement using them are
identical after definitional reduction. There are no new hypotheses, weakened conclusions,
or choices. Target signatures remain verbatim. Definition-sensitive statement review is
requested for any target depending on this abbreviation, as required by AGENTS.md section 4.

## Old

```lean
noncomputable abbrev integralTowerModules :=
  SheafOfModules.{max u (t + 1)} (completedIntegralCoefficientSheafUnrestricted l E Y)
```

## New

```lean
noncomputable abbrev integralTowerModules :=
  SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y))
```

The module also retains the standard derived localization for the original completed-ring
spelling through the proved instance `integralCompletedRingHasDerivedCategory`. Instance
matching otherwise sees only the new forgetful spelling; the unchanged consumer
`SfRationalLocalGlobalPowerTorsion` needs the original spelling explicitly. Both instances
are `HasDerivedCategory.standard` on definitionally equal categories, and introduce no
additional mathematical choice.

A separate Lean check against the repaired module compiles both identities in 2.6 s
(scratchpad/tower-defeq.log):

```lean
example : integralTowerModules l E Y =
    SheafOfModules.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E Y) := rfl
example : HEq (integralTowerHasDerivedCategory l E Y)
    (integralCompletedRingHasDerivedCategory l E Y) := HEq.rfl
```

## Users

The source-only downstream query reports 236 downstream modules and 24 textual users of
integralTowerModules. Every downstream module in the current source scan is included below. The same
definitional equality applies to archived consumers; no quarantined module is restored
or withdrawn by this packet. The equivalence argument above
applies uniformly to their signatures, even when the abbreviation is used through another
definition. The scalar-action proof adaptation is forced: its original instance search requests
SMulCommClass between the two presentations, and its original rewrite looks for the canonical
ring's restriction map while the target contains the forgetful presentation's map. Its local
scalar and CommRing annotations now use the module's coefficient presentation, and the
naturality rewrite uses erw. Its complete declaration signature and visibility stay unchanged.
The exact original compiler diagnostics and successful adapted compile are recorded in report.md.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedScalarChainShift | F3 | New helper using the same coefficient category; no earlier assertion changes. |
| Sheaf.Paper.CompletedScalarShiftDescent | F3 | New helper using the same coefficient category; no earlier assertion changes. |
| Sheaf.Algebra.Homology.RoosCommShift | F3 | New generic Roos API; the coefficient presentation does not occur in its signatures. |
| Sheaf.Algebra.Homology.ExactProductsRoosComparison | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Algebra.Homology.RingedSiteTorFlatModel | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Algebra.Homology.SitePerfectLowerModel | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Algebra.Homology.SitePerfectTorWindow | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Algebra.Homology.SitePerfectUpperModel | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.GeometricSpecializationCategory | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.MilnorTower | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.MultipointedCurveModification | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleContinuousCohomologyLimit | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleLeftComplete | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalizationFilteredSection | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence | G8 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.RoosCohomologyMaps | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.RoosCohomologyNaturality | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.RoosCohomologySequence | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.SemistableMultipointedPair | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingOperations | R5 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.CategoryTheory.SiteTorIntervalRestriction | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.CategoryTheory.Sites.CoherentConservativeReflection | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.CategoryTheory.Sites.CoherentObjectApproximation | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.CategoryTheory.Sites.CoherentToposRepair | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.AlgebraicallyClosedCoefficients | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CanonicalRingedRefinementShape | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CoefDerivedSystemEvaluationCalculus | U8 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CoefficientExtensionReductionModel | Y2 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CoefficientRingedSequenceSite | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CompleteResidueCohomologyBounds | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CompletedDirectImageLimits | P5 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CompletedKoszulQuotientRoosAugmentation | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CompletedProjectionCoherence | D2 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CompletedPullbackUnitTower | V1 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CompletedScalarShift | F3 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.CompletedTowerCorners | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.ConstantCoefficientObjectsConstructible | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.ConstructibleHeart | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.ConstructibleStandardTStructure | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.DerivedComplete | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.DerivedCompleteIntegralDetailed | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.DerivedCompleteOnSlices | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.DerivedCompleteUnrestricted | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.EtaleIntegralLineDerivedComplete | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | U1 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | V8 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.FiniteReductionReconstructionCompleted | C4 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.FiniteStagePairCategory | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.FiniteSystemPullbackCoherence | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.GeneralNearbySliceTest | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralConstructibleLinear | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralConstructibleTriangulated | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralDerivedOperations | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralDerivedOperationsOnSlices | V9 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralFinitePullbackComposition | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralHomAugmentedTowerComparison | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralHomComparisonIsIso | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralHomModelsExist | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralHomReduction | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralHomReductionComparison | C5 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralHomReductionModels | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralHomReductionTowerComponents | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralHomRoosTransport | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralLineTensorComparison | H2 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralLineTensorCompleteness | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralOperationRoosEffectivity | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralOperationsScalarExtension | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralOperationsWellDefined | R2 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralReductionTower | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralReductionTowerCanonical | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralReductionTowerWellDefined | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralScalarExtension | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralScalarExtensionConstructible | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralScalarExtensionUniverses | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralScalarExtensionWellDefined | U2 | Same category by definitional equality; signatures and mathematical assertions unchanged. Forced scalar-action proof adaptation: coefficient annotations and erw, as described above. |
| Sheaf.Paper.IsomorphismReductionTower | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.KoszulReconstruction | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.KoszulReconstructionComparison | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.ModificationsZariskiRefinement | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.NearbyClosedImage | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.NearbySpreadOut | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.NormalizedDVREffectivity | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.NormalizedDVRKFlatReductionModel | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.NormalizedDVRKFlatTransition | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrgogozoInductionData | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedClosedBaseRestriction | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedConstructibleSetSheaf | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedConstructibleSheaf | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedConstructibleSheafVanishing | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedHypercoverDescentDatum | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedMaximalPointFiniteness | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedNearbyCycles | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedProductPointsConservative | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedProperFibreExchange | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.OrientedSourceLocalization | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.PbcAutomorphismTransport | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.PbcFilteredRetractDescent | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.PbcFiniteCompletedCoefficientMap | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.PbcWeilCategory | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.PointDerivedHomEvaluation | A8 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.PointSectionsScalarExtension | G3 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.PointSectionsTensorShift | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.ProEtaleConstantReductionTower | B3 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.PurReductionLimitShiftAdjunction | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.PurTwistSheafLocallyFree | Q6 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RationalizationIdempotentComplete | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RationalizationKaroubi | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedCoefficientAssociatorShifts | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedCoefficientProjectionCocycle | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedCoefficientProjectionData | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedCoefficientPullbackCoherence | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedCoefficientPullbackComparison | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedCoefficientPullbackShifts | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedCoefficientScalarShifts | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedCoefficientScalarUnits | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedRefinementClopen | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedRefinementConstruction | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedRefinementCore | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedRefinementData | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.RingedRefinementFinite | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.ScalarExtensionComposition | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.ScalarExtensionExact | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SemilinearDerivedCalculus | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SemilinearDerivedSections | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SemilinearGeometryCore | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SemilinearGeometryDerived | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SemilinearGeometryOps | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SemilinearOperationsExistence | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SemilinearSystemModels | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SemilinearSystemsExistence | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SfDerivedCompleteLegacyComparison | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SignedLineTensorEquivalence | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.StratifiedOrientedCover | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SystemCochainTensorReduction | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SystemEvaluationFlat | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SystemNormalizedTensorClosure | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SystemOrdinaryTensorReduction | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SystemTensorMateArrows | R3 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.SystemTensorReductionFormula | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.WeilTensorProduct | J2 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.SixFunctors.CompletedTensorFiniteShift | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.SixFunctors.CompletedTensorShiftRight | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.SixFunctors.SchemeGeometricFrobenius | E8 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | C8 | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.SixFunctors.UnboundedClassicalTruncation | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ClosedImageGenericAlteration | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ContractedComponentNoExtraGeneric | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.CurveP1TreeLocalCriterion | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.FinitarySiteCoherentGenerators | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.FiniteEtaModificationGluing | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.LocalMarkingLength | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.NodalContractionNormalizationBranches | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.OrientedPointCohomology | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.OrientedPointNormalizedStratum | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ProjectiveLineTree | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ProperBaseChangeCoherentConservative | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.SemistableMarkedPoint | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ValuationReducedFibreNormalization | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | Same category by definitional equality; signatures and mathematical assertions unchanged. |
| Sheaf.Paper.IntegralReductionTowerUnrestricted | unclaimed | Definitionally equal completed-ring presentation; original spelling retains its standard localization. |

## Status

landed 20261021T011018-L-2028545 2026-10-21 (merge of deliver/F3/Sheaf.Paper.CompletedScalarShift)
