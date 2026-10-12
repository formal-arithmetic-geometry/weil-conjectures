# AbelianSheafShortExactStalkwise imports

## Reason

The theorem uses abelian-group stalks provided by Mathlib, and does not use
any declaration of `Sheaf.Topology.PresheafModuleStalkFunctor`. Removing this
unused public import prunes the presheaf-module stalk proofs from this edge
of the target closure. No statement or definition is changed. The other
imports already provide the entire theorem signature.

The second reading also removes the redundant direct public import of
`Mathlib.Algebra.Homology.ShortComplex.ShortExact`. It remains publicly
available through `Mathlib.Topology.Sheaves.Abelian` →
`Mathlib.Algebra.Category.Grp.AB` →
`Mathlib.Algebra.Homology.ShortComplex.Ab` →
`Mathlib.Algebra.Homology.ShortComplex.ShortExact`, so this removal changes
no exported declaration or instance.

## Old

```lean
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.Topology.PresheafModuleStalkFunctor
```

## New

```lean
public import Mathlib.Topology.Sheaves.Abelian
```

## Users

`tools/downstream.py Sheaf.Topology.AbelianSheafShortExactStalkwise` listed
the following modules. The five direct importers were inspected: none uses
`PresheafOfModules.stalkObj`, `stalkAddMap`, `stalkMap_linear`, `stalkMap`,
`stalkMap_id`, `stalkMap_comp`, or `moduleStalkFunctor` from the removed import.
`ConstantSubsheafPeelLayer` also imports the removed module independently.
No adaptation is required. All theorem and definition meanings, including
targets, are unchanged; this edit removes an unused re-export only. Transitive
users are included below for the shared global build to verify the import graph.

| module | group holding it | effect |
|---|---|---|
| Challenge | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineDerivedCohomology | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineDerivedConcentration | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineDerivedPushforwardConservative | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineDerivedPushforwardTExact | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineKoszulCechDerivedComparison | Z2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusShift | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | B3 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ArtinSchreierData | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ArtinSchreierDataFormulas | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ArtinSchreierExact | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ArtinSchreierExactComponents | C1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ArtinSchreierSequence | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeCurve | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeDimension | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.CoherentProjRepresentation | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.CoherentSerreVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ConstructibleCurveAnnihilator | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ConstructibleCurveQuotPart | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ConstructibleCurveSubPart | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ConstructibleCurveSubQuotient | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ConstructibleTorsionModulesAgree | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierAdditiveVanishing | H1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | K1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.BrauerAlgebraicExtension | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.BrauerFiniteModificationInjection | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.BrauerReductionInjection | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | T1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | G1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | T1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeFieldFiltration | D2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseIrreducibleOpens | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeBoundary | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | G2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBoundaryCohomology | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenComplementPullbackVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFiniteComplement | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | H2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyPullback | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPulledCounitHigh | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | N2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | P2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DisjointOpenPrimeAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | U1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FiniteCoverLowerShriekCoefficientCompatibility | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardCoefficientControl | Q1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardCohomologyComparison | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardPullbackComparison | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | M1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | P1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties | D2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | N1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeAnnihilatedPrimaryCases | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeBiproductAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeBiproductInvertible | P2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeBiproductPrimary | P2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeBiproductUnconditional | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeFieldFiltration | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeTorsionNonunitCohomology | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ReductionModuleAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ReductionUnitsKernelVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.RetractAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.RootTrivializationBaseChange | P1 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.SepClosedComparison | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.SepClosedComparisonCore | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.SepClosedComparisonCurve | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | A2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.UnderlyingAbelianAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.UniversalHomeomorphismAssertions | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.CurveCoefficientPair | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.CurveCohomologyConnectedReduction | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTorIndependentFlatComplex | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DivisorLineBundleAgreesSC | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DivisorModule | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DivisorModuleLocal | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.EtaleZariskiCohomology | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | Q2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteFlatProperSupportDescent | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FinitePushforwardLocallyFree | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FlatModuleDescent | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteFibreVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FormalFunctionsStalk | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GenericRankLeadingDegree | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GenusInvariant | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GenusWellDefined | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GlobalSectionsProperVariety | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GmPicardPullback | R2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GradedSerreVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.HilbertDifference | Z2 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.IntersectionEffectiveCartier | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.IntersectionNumber | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.KoszulAffineDetection | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.LocalDvrBaseChange | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.LocallyFreeExtNaturality | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Modules.VeryAmpleDisjointUnion | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.NumericalPolynomialLeadingTerm | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorPullback | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PerfectHomGap | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Picard.ArrowIsoTensorPullbackCounit | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeIsIso | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Picard.InvertibleDirectImageClasses | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardH1RestrictionCompatibility | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardLift | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDualityPairingNaturality | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition | A3 | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperGlobalSectionsFlatBaseChange | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperNormalizedFibres | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.QCohComplexAlternatingCechDerivedSections | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.RationalSectionDivisor | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.RationalSectionOrder | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.RelativeSerreVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SerreSectionModuleFinite | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SmoothProjectiveCurveConnected | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SteinUniversallyClosedFactor | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.TopDimensionalReductionIntersection | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.VanishingProjective | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.VeryAmpleSeparationCriterion | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ZariskiDimensionBound | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ZeroDimensionalBaseChangeGeometricPoints | none | Transitive importer; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ZeroDimensionalPullbackGlobalSections | none | Transitive importer; no statement or definition changes. |
| Sheaf.CategoryTheory.Sites.TorsorExtensionPushforward | none | Transitive importer; no statement or definition changes. |
| Sheaf.CategoryTheory.Sites.TorsorH1Functoriality | none | Transitive importer; no statement or definition changes. |
| Sheaf.CategoryTheory.Sites.ZariskiTorsorExtensionPushout | none | Direct importer; no use of removed declarations; no adaptation. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | none | Transitive importer; no statement or definition changes. |
| Sheaf.Paper.BaseChangeClosureComponents | none | Transitive importer; no statement or definition changes. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Transitive importer; no statement or definition changes. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | none | Transitive importer; no statement or definition changes. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none | Transitive importer; no statement or definition changes. |
| Sheaf.Paper.QCohAcyclicDerivedSectionsComparison | none | Transitive importer; no statement or definition changes. |
| Sheaf.Paper.SupportDimensionCohomologyVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | ORCHESTRA | Transitive importer; no statement or definition changes. |
| Sheaf.Topology.ClosedImmersionPushforwardExact | none | Direct importer; no use of removed declarations; no adaptation. |
| Sheaf.Topology.ClosedPushforwardBoundaryNaturality | none | Transitive importer; no statement or definition changes. |
| Sheaf.Topology.ClosedUnionCohomologyVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.Topology.ConstantSubsheafFiniteFiltration | none | Transitive importer; no statement or definition changes. |
| Sheaf.Topology.ConstantSubsheafPeelLayer | none | Direct importer; no use of removed declarations; no adaptation. |
| Sheaf.Topology.FiniteClosedCoverCohomologyVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.Topology.IrreducibleIntegerExtensionVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.Topology.NoetherianCohomologyDimOne | none | Transitive importer; no statement or definition changes. |
| Sheaf.Topology.NoetherianExtensionByZeroReduction | none | Transitive importer; no statement or definition changes. |
| Sheaf.Topology.NoetherianOpenClosedCohomologySequence | none | Direct importer; no use of removed declarations; no adaptation. |
| Sheaf.Topology.NoetherianTopologicalCohomologyVanishing | none | Transitive importer; no statement or definition changes. |
| Sheaf.Topology.NoetherianVanishingByIrreducibleComponents | none | Transitive importer; no statement or definition changes. |
| Sheaf.Topology.SliceOpenClosedShortExact | none | Direct importer; no use of removed declarations; no adaptation. |
| TargetsCheck | none | Transitive importer; no statement or definition changes. |
| WeilConjectures | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Cohomology.Projective | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Cohomology.Serre | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Assertions | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.BoundaryNeighbourhood | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Brauer | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.DivisorSequence | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | A2 | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | C1 | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Modules.AffineHom | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Modules.Ample | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Picard.Degree | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Picard.RationalPoint | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Picard.Representability | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Duality | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryConstruction | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LFunction | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.FourierTransform.AffineSpace | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.FourierTransform.Defs | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.FourierTransform.Inversion | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.FourierTransform.Perverse | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties.Stalk | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Gabber | Q2 | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none | Transitive importer; no statement or definition changes. |
| WeilConjectures.ZetaFunction.HasseWeil | none | Transitive importer; no statement or definition changes. |

## Status

landed 20261012T085346-L-42300 2026-10-12 (merge of deliver/U1/Sheaf.Topology.AbelianSheafShortExactStalkwise)
