# fppfSheafRepresentabilityDescentData proof-local elaboration commands

## Reason

The completed proof adds fully proved private categorical helpers. They require additional
universe names and the backward elaboration settings used throughout this library.
The stage-3 static command comparison requests a record for these commands. These settings
control elaboration in this module; importers do not inherit them. Universe names are local
parameters, and the public theorem still quantifies only over its original universe `u`.
No public signature, definition, visibility, attribute, or public import changes.
The repair preserves C7’s intervening canonical proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`; the proof has been reapplied to
the current source rather than repushing the returned head `516810ce197`.

## Old

```lean
set_option autoImplicit false

universe u
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u z v w
```

The two constraint helpers also scope `backward.isDefEq.respectTransparency false`
locally. The remaining additional declarations are private and completely proved.

## Users

`tools/downstream.py` reports the following transitive importers. Its `--uses` scan
finds one consumer of the public theorem, `FppfFamilyAffineEffectivityReduction`, at
two applications. The unchanged signature means both applications are preserved.
No consumer source needs modification. No target changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData | F7 | Proof completed; signature unchanged |
| Sheaf.AlgebraicGeometry.AbelianCoherentExteriorBaseChange | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ActionGroupoidTorsorComparison | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AdequateBaseChangeAffinization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AdequateClosedSubstackAffinization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AdequateRelativeSpectrum | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AdmissibleFreeFiniteQuotient | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AffineActionQuasicoherentDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AffineActionStackPresentation | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AffineGroupTorsorStackification | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AffineLciConormalSplitting | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AffinePGLQuotientOrbitTopology | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AffineStackStabilizerEtaleComparison | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineLimits | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSourceUnramifiedBaseOpen | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentSupportUnionSequence | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentTwoOfThreeDevissage | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceCohomologyAboveDimension | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceConstructibleAffineEtaleTest | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseAffineImmersion | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseSchemeOpen | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleAffinePairsQuasiSeparated | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceExtendAdmissibleBlowup | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteTypeSubmoduleExtension | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcQCSeparatedDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceHigherDirectImageQuasiCoherent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceLargestSchematicOpen | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceNoetherianChevalleyImage | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceNoetherianCoherentAcc | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceProperFpqcDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceQcqsSpectral | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiAffineAffineFactorization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactCancellation | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceReducedSupportGenericIdealInclusion | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeIntegralFactorization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceSchematicNearHeightOne | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceSerreAffineness | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceUniversalSurjectiveFlatOpen | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceWeakChow | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicStackRimSchlessinger | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ArithmeticNodalCurveStackSmooth | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ArtinNoetherianVersalBaseChange | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ArtinVersalBaseChangeSmooth | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ClosedRelationSchematicNeighbourhood | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ConstructibleClosureFibreAvoidance | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.CurveFormalEffectivity | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.CurveSmoothPolarizationCover | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.DivideFiniteFlatSubgroupoid | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.DmFiniteInertiaAffineRelation | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.DmLocallyQuasiFiniteAtlasTest | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.DmQuasicompactAtlasCriterion | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ElementaryEtaleShriekExact | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleAffineQuotientRepresentable | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleAtlasDistinctTupleGeometry | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleConfigurationExteriorHom | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleDescentCompositionRefinement | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleMonomorphismOpen | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleQuasiAffineImageScheme | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleRelationQuotient | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleSaturationQuasiAffinePullback | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleSheafSpaceAtlasBootstrap | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleStabilizerPreservingAffineModuli | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FieldMonomorphismFiniteChartDecencyCriterion | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteDiagonalizableSubgroupParameter | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteGroupQuotientAtlasTorsor | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteInertiaFlatQuasifinitePresentation | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteLocallyFreeFibreSchemeNeighbourhood | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FinitePointSelfRelationFieldMonomorphism | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FlagCohomologyFiniteExact | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FlatAffineActionAlgebraDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FlatAffineActionStackPresentation | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FlatGroupoidQuotientOpenPresentation | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FlatLfpSpacePushoutGluing | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FlatSpaceDerivedExternalCup | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FlatSpaceSmoothLocus | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FlatSpaceSplitDeformationExt | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FpEtaleSpaceDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FpSpaceAffineLimitCategory | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FpSpaceQcqsBaseLimitDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FppfRelationEtaleReplacement | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FppfSpaceAtlasBootstrap | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.FreeFiniteSpaceQuotientSeparated | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GeometricAffineNeighbourhoodSchemeDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GerbeQcDiagonalDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.AbelianSubgroupEquivariantMultipleMap | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.BorelCharacteristicPicardSequence | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.BorelHomomorphismRigidity | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientAffineCell | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientProperGeometry | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.BorelSchemeNormalizer | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.BottSamelsonGalleryGeometry | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.FieldParabolicQuotientRationalLift | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.FlagEffectivePicardGenerators | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.FlagLineEquivariantSerrePairing | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.FlagTorusFixedGeometry | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.FrobeniusAdjacentBorelReflection | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.FrobeniusBorelInductionGeometry | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineSchubertCurveDegree | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotientKrullDimension | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.LocalBorelQuotientGeometry | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.LocalParabolicCocharacterDescription | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.MinimalParabolicFlagProjection | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.MultiplicativeIsogenyBorelComparison | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.NestedHomogeneousQuotientGeometry | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.NilpotentBorelEqualsGroup | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.QuotientBorelTorusImages | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.RankOneAdjointProjectiveLinear | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.ReductiveCocharacterParabolicGeometry | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.RelativeAdjointRankOneFlagCurve | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.SchubertClosureCellGeometry | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.SmoothAffineNormalQuotient | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.SplitBruhatAffineStratification | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.StandardParabolicLeviCharts | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.StrictDominantFlagLineAmple | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.TorusNormalizerBorelTransitivity | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.TrivialKernelHomogeneousQuotient | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.WeylReflectionRealization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralSpaceFinitePresentationLimit | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.InvariantOpenSubstackDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothOpen | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.KeelMoriFiniteInertiaQuotient | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.KeelMoriStabilizerPreservingEtale | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.KeelMoriUniformTopologicalModuli | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.LocallyQuasiFinitePseudoTorsor | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.NodalRelativeDualizingLine | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.NormalTorusFiniteEtaleSplitting | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.OpenImageQuasiAffineSchemeDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.OpenSeparatedEtalePushout | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardTrivialMultiplicativeCover | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.PolarizedFineLogEtaleDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.PowerLiftingAdequateAffineQuotient | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.PowerLiftingQuotientSubmersive | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.PresheafSpaceTargetBootstrap | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLogRegularResolution | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectivePGLInvariantQuotient | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperCurveAutomorphismScheme | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperSpaceCurveQcohBound | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperSpaceFiniteImageNeighbourhood | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.QcStackSpectralPointSpace | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.QcqsSpaceFiniteSchemeCover | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.QcqsSpaceIntegralSchemeCover | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.QcqsSpaceMonomorphismQuasiAffine | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.QuasiCompactSpaceSchematicStrata | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.QuasiCompactSubtrusiveEtaleDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.QuasiDmFlatLocallyQuasiFiniteAtlas | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ReducedSingletonFieldFactorization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ReducedSingletonQcDiagonalGerbe | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.RelativeAffineMultiplicativeQuotient | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.RelativeFiniteHilbertLciLift | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.RepresentableLocallyQuasiFiniteCalculus | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.RepresentableStackDiagonalCriterion | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.RepresentableStackQuasicompactTests | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SectionMarkedFinitePartsScheme | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SeparatedGroupSpaceGeometricScheme | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SeparatedLqfAffineRelationCover | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SeparatedSpaceHomeomorphismIntegral | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothIntegralFibreVerticalDivisors | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothSpaceProperComponentNeighbourhood | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAbsoluteNoetherianApproximation | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAffineBaseHigherImageSections | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAffineChartUniformQcohVanishing | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAffineCupMaps | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAffineFinitePresentationLimit | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAffineFormalFunctions | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAffineLocality | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAffineModuleCorrespondence | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAffineRelativeCupSections | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAlternatingSignCohomologySpectral | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceAssassinContainmentConstructible | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceCoheratorDistinguishedSquareTriangle | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceCoherentFormalEffectivity | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceCoherentPushout | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceCompleteDevissageFibreNeighbourhood | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceComponentGenericChartDimension | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceConnectivePerfectSectionsAffine | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceConormalFlatnessCriterion | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceCountableHypercohomology | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceDerivedCoheratorBound | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceDerivedDirectImageCoproducts | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceDerivedHomMayerVietoris | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceDistinguishedDerivedGluing | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceEtaleClosedDegreeLoci | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceEtaleFiniteFpEnvelope | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceEtaleIdealFactor | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceEtaleMaximumDegree | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceEtalePullPushRetract | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceEtaleSheafRealization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceEventualMonomorphism | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceFirstOrderRingedDescription | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceFlatMonomorphismRepresentable | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceFlatteningByAdmissibleBlowup | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceGeneratorDetectsLowerBound | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceGenericFreeness | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceGlobalIdempotentClopen | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceH1SeparateClosed | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceIntegralFactorizationEtaleBaseChange | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceIntegralQcqsPermanence | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceInvariantOpenQuotient | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceInverseModulePerfectTests | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceInverseModuleProperShrinking | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceInverseModulesNearSpecialFibre | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceLimitOpenCoverDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceLimitSchematicStage | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceMaximalFlatLfpBaseOpen | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceMeromorphicGenericChartModel | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceModuleSurjectivityOpen | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceNoetherianModuleHom | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceNoetherianPseudoCoherentCriterion | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceNormalizationQuasiFiniteLocus | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePerfectExtWindow | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePerfectLimitCategory | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePerfectOpenRetract | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePerfectSourceHomContinuity | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePerfectTensorGlobalLimits | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePerfectTensorTestHolim | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePerfectTensorTestsUpperBound | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePerfectUniformTor | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePicardStackSmooth | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePowerLiftingAffineness | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceProjFiniteDegreeEquations | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceProperArbitrarySchemeTests | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceProperCoherentHigherImages | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceProperSupportClosedOperations | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceProperSupportDerivedProjectionFormula | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceProperSupportUniversalFlattening | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceProperSupportUniversalPurity | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePureDimensionFlatnessRepresentability | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePushoutCompatibleEtaleCharts | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePushoutEtaleBaseChange | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePushoutEtaleMorphismCriterion | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpacePushoutLiftedAtlas | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceQcOpenEnlargementInduction | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceQcqsDerivedProjectionFormula | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceQcqsDistinguishedSquareInduction | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceQcqsSplittingFiltration | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceQuasiCoherentTorAmplitudeTest | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceQuasiCompactImmersionLocality | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceQuasiFiniteLocusOpen | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceReducedGenericFlatFinitePresentation | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceRelativeAmplenessFpqcDescent | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceRelativeFlatModulePushout | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceRelativeLciSourceLocus | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceSchemeAfterFieldExtension | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceSchemehoodLocalRingTest | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceSepClosedComponentsBaseChange | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceSeparatedEtaleDiagonalComplement | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceSingleComplexBaseChange | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceSmoothSourcePointLocality | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceSquareZeroRingedRealization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceSupportedApproximationSquareStep | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceSupportedKoszulHighLocalization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceSupportedKoszulLowLocalization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceSupportedPerfectApproximation | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceUniversalConormal | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceUniversallyClosedQuasiCompact | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceUnramifiedLocusBaseChange | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceUnramifiedRadicialParameterOpen | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceUnramifiedRadicialRepresentable | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceValuationLineTriviality | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceZariskiAfterAdmissibleBlowup | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SplitTorusNormalizerQuasiAffineQuotient | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.StackQuasiFiniteFibreNeighbourhood | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.StackQuasiSeparatedCancellation | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.StackSeparationComposition | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.StackTopologyOpenSubstacks | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.StackUnramifiedLocusBaseChange | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.StackVersalRingExistence | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SubtrusiveTopologicalDescentCalculus | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.SupportedEtaleExcision | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ThickeningOfSchemeSpace | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.TraitPrimeToEllLogAlteration | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.TraitSpaceClosureThickeningsScheme | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.TranslateBadTupleDimension | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.UniversalConormalChartTransitivity | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.UniverseEnlargedEtaleRealization | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.UnramifiedLciKoszulEtaleCharts | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.WeilRestrictionGeometricProperties | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.AlgebraicGeometry.ZeroDimensionalFieldSpaceComponents | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.Paper.NormalLatticeFiniteCoverPresentation | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.Paper.TameIntegralReductionFamily | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.SecPurity.NormalLocallyConstantFiniteSection | unclaimed | None: same public signature and imports; no adaptation |
| Sheaf.SecTraceFormula.SeparatedLqfFppfEffectiveDescent | unclaimed | None: same public signature and imports; no adaptation |

## Status

landed 20261024T214349-L-598454 2026-10-24 (merge of deliver/F7/Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData)
