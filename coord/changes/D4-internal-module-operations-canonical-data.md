# InternalModuleOperations canonical data and compiler performance

## Reason

The repeatedly expanded square isomorphisms made the complete transport coherence proof
exceed the standard single-file compiler limit. internalSquare and sectionSquare now
project from squareData, a record storing their original two compositor/equality/compositor
expressions with their proved component compatibility; both are `rfl`-equal to the old
formulas. ring, equivalence, upperStar and adjunction stay reducible `abbrev`s with their
published bodies and only gain explicit type ascriptions; lowerStar is unchanged.
(Reviewer FIX: the delivered `def` versions, the re-packaged equivalence structure and the
type ascription on lowerStar hid instances that importers find through the abbreviations:
HasDerivedCategory on `SheafOfModules (ring Λ T)`, `(equivalence Λ T).functor.Additive`,
`(pullback Λ f).Additive`, and IsRightAdjoint/limit preservation of lowerStar under
`respectTransparency true`; OpenInternalKFlatMateNormalization, SectionDerivedTensorData
and SupportedCommonFieldScalarData failed to compile.) No data are chosen from an
existence theorem. No target statement changes meaning.

## Old

```lean
noncomputable abbrev ring (T : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T))
```

```lean
noncomputable abbrev equivalence (T : Scheme.{u}) :=
  sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T)
```

```lean
noncomputable abbrev upperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.forget (ring Λ Y) ⋙
    PresheafOfModules.pullback.{u + 1} (F := siteMap f) (coefficientMap Λ f).hom ⋙
      PresheafOfModules.sheafification (R₀ := (ring Λ X).obj) (𝟙 (ring Λ X).obj)
```

```lean
noncomputable abbrev adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.PullbackConstruction.adjunction.{u + 1}
    (F := siteMap f) (coefficientMap Λ f)
```

```lean
noncomputable def internalSquare {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g) :
    CondensedRing.upperStar Λ j ⋙ CondensedRing.upperStar Λ g' ≅
      CondensedRing.upperStar Λ g ⋙ CondensedRing.upperStar Λ j' :=
  (CondensedRing.upperStarComp Λ g' j).symm ≪≫
    eqToIso (congrArg (CondensedRing.upperStar Λ) sq.w) ≪≫
      CondensedRing.upperStarComp Λ j' g
```

```lean
noncomputable def sectionSquare {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g) :
    upperStar Λ j ⋙ upperStar Λ g' ≅ upperStar Λ g ⋙ upperStar Λ j' :=
  (upperComp Λ g' j).symm ≪≫ eqToIso (congrArg (upperStar Λ) sq.w) ≪≫ upperComp Λ j' g
```

## New

```lean
noncomputable abbrev ring (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T))
```

```lean
noncomputable abbrev equivalence (T : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ≌
      SheafOfModules.{u + 1} (ring Λ T) :=
  sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T)
```

```lean
noncomputable abbrev upperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules.{u + 1} (ring Λ Y) ⥤ SheafOfModules.{u + 1} (ring Λ X) :=
  SheafOfModules.forget (ring Λ Y) ⋙
    PresheafOfModules.pullback.{u + 1} (F := siteMap f) (coefficientMap Λ f).hom ⋙
      PresheafOfModules.sheafification (R₀ := (ring Λ X).obj) (𝟙 (ring Λ X).obj)
```

```lean
noncomputable abbrev adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar Λ f ⊣ lowerStar Λ f :=
  SheafOfModules.PullbackConstruction.adjunction.{u + 1}
    (F := siteMap f) (coefficientMap Λ f)
```

```lean
noncomputable def internalSquare {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g) :
    CondensedRing.upperStar Λ j ⋙ CondensedRing.upperStar Λ g' ≅
      CondensedRing.upperStar Λ g ⋙ CondensedRing.upperStar Λ j' :=
  (squareData Λ sq).internal
```

```lean
noncomputable def sectionSquare {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g) :
    upperStar Λ j ⋙ upperStar Λ g' ≅ upperStar Λ g ⋙ upperStar Λ j' :=
  (squareData Λ sq).sectionwise
```

The new public import Sheaf.CategoryTheory.CompatibleSquareComponents exposes the record
used by the squareData definition. New public proved interfaces are square_pasting, CompatibleSquareComponents,
compatibleSquareComponents, upperComp_compatible and squareData. The generic square record
is owned by lem-sfb-compatible-square-components; the scheme specialization and compositor
compatibility are owned by lem-sfb-internal-module-operations-transport. The record proof
fields use the existing normalized mate compositor theorem and elementary pasting.

File-local proof options disable backward defeq attributes and permit type reduction during
proof elaboration; they do not change imported instances or declaration signatures.
The source library and all existing public imports are preserved.

## Users

The following is the conservative textual user inventory from tools/downstream.py --uses
ring equivalence lowerStar upperStar adjunction internalSquare sectionSquare. Last-component
matching includes unrelated names; listed users retain the same canonical operations.
No consumer edit is necessary by mathematical meaning; unchanged consumer compiles are
reported in report.md. The two square formulas are preserved through the record fields.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology | P7 | Same canonical data; textual hits: ring, lowerStar, upperStar, adjunction. |
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Same canonical data; textual hits: equivalence, lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportComparison | X9 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportData | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.FieldScalarProjectionMateCoherence | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | D4 | Same canonical data; textual hits: ring, equivalence, lowerStar, upperStar, adjunction, internalSquare, sectionSquare. |
| Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel | unclaimed | Same canonical data; textual hits: ring, equivalence, lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.LisseModuleInverseImage | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.AlgebraicGeometry.NativeAdicAffineOpenZeroStratification | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | G2 | Same canonical data; textual hits: upperStar. |
| Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.AlgebraicGeometry.QcqsClosedPullbackFiniteModelCompletion | G6 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.QcqsProperLocalizingCoproducts | unclaimed | Same canonical data; textual hits: equivalence, lowerStar. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryFunctor | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Compactification.NagataDensityNormalization | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | C8 | Same canonical data; textual hits: equivalence. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCompactificationSheafScalarMap | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleScalarSectionNormalization | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafFoldScalar | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.AdmissibleCupCoefficientPassages | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AffineCoefficientCounitNormalization | C1 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AffineCounitScalar | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | W9 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | K4 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AffineProfiniteFamilySerreCd | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.AffineProperSquareStratifiedModule | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | J1 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | F7 | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.BoundaryFiniteSiteRealization | unclaimed | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.BoundaryFiniteTorDomains | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.BoundedFlatTensorContinuity | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.BoundedSiteExchangeTransposes | D3 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.BoundedSiteTensorTransposes | V9 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Same canonical data; textual hits: equivalence, lowerStar, upperStar. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.ChartDncVectorFactors | S9 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ChartExceptionalMateCoherence | W3 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| Sheaf.Paper.ClopenCompletedTowerRestriction | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ClopenStrictSystemSupport | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| Sheaf.Paper.ClopenSystemRealizationData | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ClosedCoefficientTransposeCocycles | unclaimed | Same canonical data; textual hits: ring, lowerStar, adjunction. |
| Sheaf.Paper.ClosedSectionCompactOrigin | B9 | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ClosedSupportExceptionalMate | unclaimed | Same canonical data; textual hits: lowerStar, upperStar, adjunction. |
| Sheaf.Paper.ClosedTestComparisonTestNaturality | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ClosedTestDerivedComparisonNormalization | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ClosedTestLocalizedModelCoherence | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ClosedTestLocalizedModelData | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ClosedTestLocalizedRestrictionNormalization | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ClosedTestUnitEvaluation | unclaimed | Same canonical data; textual hits: ring, equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.ClosedTorsionRigiditySerreTransfer | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.CoefDualizingClosedChart | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.CoefFiniteHomSiteDescent | C5 | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.CoefTowerCoaugmentation | R5 | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.CoefficientDualizingOpenAdjoint | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.CoefficientDualizingOpenTensor | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.CoefficientHeartLocallyClosedExtension | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.CoefficientPathNormalization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.CoefficientProjectionSquare | unclaimed | Same canonical data; textual hits: equivalence, lowerStar, upperStar. |
| Sheaf.Paper.CoefficientPushFilteredLegs | unclaimed | Same canonical data; textual hits: equivalence, upperStar. |
| Sheaf.Paper.CoefficientScalarTensorRealization | J3 | Same canonical data; textual hits: ring, equivalence, upperStar, adjunction. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | V8 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.CompactSupportCoefficientModels | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | M2 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y5 | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.CompactSupportExchangeDomains | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.CompactSupportProjectionFormula | S4 | Same canonical data; textual hits: ring. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Same canonical data; textual hits: ring, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.CompactSupportStrictScalarMate | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.CompactSupportSystemTransposeNormalization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.CompactificationCompletedRealizationData | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.CompactificationStrictRealization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.CompleteCompactificationLimitRealization | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.CompleteCompactificationLimitSupport | unclaimed | Same canonical data; textual hits: ring, equivalence, adjunction. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.CompositeModuleOplaxMate | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.CompositionTensorMate | G8 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ConcreteProjectionReductionSquare | D7 | Same canonical data; textual hits: ring. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.CondensedTateIntegralTower | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.ConstantScalarTowerAdjunction | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ConstructibleCoefficientSiteSquare | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Same canonical data; textual hits: equivalence, upperStar. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | D6 | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Same canonical data; textual hits: ring, equivalence, lowerStar. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ConstructibleTensorComposition | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ContinuousAlgClFiniteStageDevissage | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | P3 | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ContinuousAlgclScalarExtensionConstructible | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ContinuousModuleSectionModel | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ContinuousQbarNormalizedSheafFiltration | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.CountableNormProjectionCriterion | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | G9 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Same canonical data; textual hits: equivalence, lowerStar. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Same canonical data; textual hits: equivalence, lowerStar. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.DiagonalCompletedFrame | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.DiagonalCompletedPushSquare | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.DiagonalExchangeCube | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.DiagonalOrientationRefinement | T8 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.DiagonalQuotientBaseChange | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.DiagonalTowerLimit | V2 | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Same canonical data; textual hits: lowerStar, adjunction. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Same canonical data; textual hits: lowerStar, adjunction. |
| Sheaf.Paper.DirectImageHomEvaluationSquare | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.DualBaseChange | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.EquivariantAdicFibreData | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| Sheaf.Paper.EquivariantAdicFibreNaturalityData | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.EquivariantAdicFibreRealizationData | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.EtaleBrownEvaluationMate | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.EtaleBrownGeometricComparisons | unclaimed | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.EtaleBrownProjectionRealization | unclaimed | Same canonical data; textual hits: equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.EtaleCartesianTowerTensorComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | E1 | Same canonical data; textual hits: ring, equivalence, adjunction. |
| Sheaf.Paper.EtaleCompactScalarBaseChange | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.EtaleCompactScalarCoherence | Q3 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.EtaleCtfChartDomain | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.EtaleDirectImageScalarComposition | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.EtaleLisseHomReduction | E8 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.EtaleOpenScalarExchange | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.EtaleOpenScalarExchangeSquare | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.EtaleOriginScalarProjectionSquare | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y7 | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.EtaleProEtaleScalarCounitTransposes | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.EtaleProEtaleScalarMate | T7 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.EtaleProEtaleScalarPullbackCube | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.EtaleProperCoefficientTensorUnit | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.EtaleScalarPullbackIdentityNormalization | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.EtaleSingleCoefficientProjection | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.EtaleSumCoefficientComputation | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.EtaleSystemBrownConstruction | unclaimed | Same canonical data; textual hits: equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.EtaleSystemCoefficientProjection | unclaimed | Same canonical data; textual hits: lowerStar, adjunction. |
| Sheaf.Paper.EtaleSystemCofinalData | unclaimed | Same canonical data; textual hits: ring, equivalence, adjunction. |
| Sheaf.Paper.EtaleSystemCofinalMate | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.EtaleSystemImageTensor | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.EtaleSystemProjectionData | unclaimed | Same canonical data; textual hits: lowerStar, upperStar, adjunction. |
| Sheaf.Paper.EtaleSystemScalarMateCoherence | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.EtaleTowerBrownAdjunction | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ExceptionalCoefficientComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ExceptionalCoefficientMaps | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ExceptionalDualizingBaseChangePasting | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ExceptionalFieldDescent | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ExceptionalFiniteScalarMates | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Same canonical data; textual hits: equivalence, adjunction. |
| Sheaf.Paper.ExceptionalOriginAdjunctionEvaluation | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ExceptionalSiteOriginComparison | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ExceptionalSystemInterfaces | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ExceptionalSystemTransport | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ExchangeFunctoriality | F6 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FdCompletedCompositorNormalization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FieldLisseStratifiedHeartSupport | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FieldScalarNormalizedSystems | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.FieldScalarReductionData | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.FieldScalarSystemData | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FilteredFlatTensorCohomology | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | P8 | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.FiniteCoefficientDerivedExchangeIdentification | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteCoefficientDirectImage | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteCoefficientModelComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FiniteCompactSiteCoherence | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.FiniteCompactSupportEvaluationRefinement | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteComplexHeartFilteredApproximation | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteDiscreteEncodingCompactification | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteDiscreteEncodingConstructibility | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteDiscreteEncodingPullbackFixed | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.FiniteExceptionalSiteNormalization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar, adjunction. |
| Sheaf.Paper.FiniteFieldClosedSupport | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Same canonical data; textual hits: ring, lowerStar, upperStar. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Same canonical data; textual hits: equivalence, lowerStar. |
| Sheaf.Paper.FiniteFreeDerivedScalarCalculus | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FiniteFreeHomLocalCalculation | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same canonical data; textual hits: ring, lowerStar, upperStar. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteHomDomainCalculus | G7 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteKernelConstructibleLocalization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteLevelProjectionFactors | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteMateDomain | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteModelSheafQuotientConstructible | G4 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FinitePointReconstructedEvaluationSquare | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteRingRelativeScalarComparison | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.FiniteScalarLocalModelComplete | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | U8 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteSiteTowerPaste | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.FiniteSiteWordRefinement | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteSpanModuleDerivedComparison | X8 | Same canonical data; textual hits: ring, equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.FiniteStageSupportedGeneration | Z9 | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.FiniteStrataCompletionDetection | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteTargetChangeCoherence | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FiniteTateBalancedScalarPullback | H2 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | G3 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FiniteTwistRootTrivialization | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FiniteWindow | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.FlatCoefficientSquareNormalization | unclaimed | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.FlatScalarUnitNormalization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Same canonical data; textual hits: lowerStar, upperStar, adjunction. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Same canonical data; textual hits: equivalence, lowerStar, upperStar. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.FreeParameterDegreeZeroData | unclaimed | Same canonical data; textual hits: lowerStar, adjunction. |
| Sheaf.Paper.FreeParameterEvaluationCoherence | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FreeParameterEvaluationData | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FreeParameterRelativeMaps | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.FreeParameterScalarMaps | unclaimed | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | M3 | Same canonical data; textual hits: ring. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.FrobeniusSquareExchange | H6 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.GeneralChartComparisons | G6 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.GeneralLfpAdicInputWitness | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.GlobalInternalHomDetection | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.GlobalVerdierDuality | T2 | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | J8 | Same canonical data; textual hits: equivalence, lowerStar, upperStar. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | C8 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralAdicInputNormalization | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Same canonical data; textual hits: equivalence, lowerStar. |
| Sheaf.Paper.IntegralCoefficientSquareNormalization | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | F8 | Same canonical data; textual hits: ring. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralCriterionReductions | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Same canonical data; textual hits: equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.IntegralExceptionalInverseImage | V6 | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.IntegralFibreSectionSpecialization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.IntegralFiniteScalarPerfectModel | unclaimed | Same canonical data; textual hits: equivalence, upperStar. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | D5 | Same canonical data; textual hits: ring, equivalence, adjunction. |
| Sheaf.Paper.IntegralGeneralLfpSequentialContinuity | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralHenselianLisseSectionRigidity | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.IntegralModels | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | G8 | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Same canonical data; textual hits: equivalence, lowerStar. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | D7 | Same canonical data; textual hits: ring, equivalence, sectionSquare. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.IntegralQuotientPullbackFaceModel | R8 | Same canonical data; textual hits: ring, equivalence, upperStar. |
| Sheaf.Paper.IntegralQuotientSectionMateRealization | S5 | Same canonical data; textual hits: ring, equivalence, adjunction. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.IntegralSupportFunctorNormalization | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.IntegralTensorProduct | D5 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralTensorPullback | A9 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | V7 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.IntegrationTransposeScalarMate | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.InternalDirectImageLaxRealization | unclaimed | Same canonical data; textual hits: ring, equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.InternalOplaxResolvingComponents | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.InternalPullNormalizationExistence | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.InternalScalarProjectionMate | unclaimed | Same canonical data; textual hits: ring, equivalence, upperStar. |
| Sheaf.Paper.InternalScalarPullbackNormalizationData | unclaimed | Same canonical data; textual hits: ring, equivalence, adjunction. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.IsomorphismFiniteExchangeCoherence | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerBarResolution | unclaimed | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerNormalizedComparison | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerPartialNerveChart | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerPartialNerveMorphism | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerPartialNerveScalarMorphism | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerRefinement | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerResolutionColumns | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.KummerScalarRestriction | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerStratumScalarMaps | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerStratumScalarMateDetection | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.KummerSuccessiveDescent | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.KummerTermMate | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.LatticeSubquotientFiltration | R9 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.LevelwiseNormalizedStrictSystems | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.LineKummerFieldRealization | P9 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.LineZeroClassExchange | Z6 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Same canonical data; textual hits: equivalence, lowerStar. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Same canonical data; textual hits: ring, equivalence. |
| Sheaf.Paper.LocallyFiniteCoefficientRingRealization | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.MateOpenCompactSupportExchange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.MateOpenProperRestrictionIso | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.MateOpenProperSupport | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.MateOpenRestrictionMaps | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.MixedCupCoefficientData | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.MixedCupNormalizedScalars | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Same canonical data; textual hits: equivalence, upperStar. |
| Sheaf.Paper.ModuleSectionDerivedComparisonSquare | unclaimed | Same canonical data; textual hits: ring, equivalence, lowerStar, adjunction. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.NativeConstantSupportModel | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.NativeEncodingDerivedOperations | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.NativeModuleConstructibilityComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.NativeOpenDerivedTensor | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.NativeScalarRestrictionComparison | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.NativeWeilInductionComparisonData | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Same canonical data; textual hits: ring, equivalence. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Same canonical data; textual hits: ring, equivalence, adjunction. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.NoetherianTorsionCdTopologicalSerreTransfer | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.NonaffineClosedTestExchangeIdentification | H8 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.NormAlgclOrderedFiniteModelFiltration | R2 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.NormalizedDerivedIsomorphismTransport | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.NormalizedInternalSupportScalars | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.NormalizedScalarRestrictionPush | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.NormedPointExactMonoidal | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Same canonical data; textual hits: equivalence, upperStar. |
| Sheaf.Paper.OpenInternalKFlatMateNormalization | unclaimed | Same canonical data; textual hits: ring, equivalence, upperStar, adjunction. |
| Sheaf.Paper.OpenProEtaleCounitScalar | F3 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.OpenScalarSiteCoherence | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.OpenSquareSupportScalarCounit | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.P1CounitScalar | F4 | Same canonical data; textual hits: lowerStar, upperStar, adjunction. |
| Sheaf.Paper.P1KummerTraceSiteTransport | W8 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.PadicAlgClConstructibleScalarRestriction | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.PodReconstructionRawRationalNaturality | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.PointSignedCyclotomicAction | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | H2 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | E5 | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | C5 | Same canonical data; textual hits: ring, equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.ProEtaleVectorIntegration | N1 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProfiniteConstantDerivedFunctions | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProfiniteDerivedEvaluation | unclaimed | Same canonical data; textual hits: lowerStar, upperStar, adjunction. |
| Sheaf.Paper.ProfiniteFreeSliceDerivedHom | unclaimed | Same canonical data; textual hits: ring, equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.ProfiniteGeometricFamilyHeartCd | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Same canonical data; textual hits: equivalence, adjunction. |
| Sheaf.Paper.ProjectionReductionWitnessedFlatDomains | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProjectiveDiagonalComposition | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperBaseChangeRational | F1 | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperCoefficientDescent | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ProperEtaleOriginScalarData | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperEtaleOriginScalarIsomorphism | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Same canonical data; textual hits: ring, equivalence, upperStar. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperHeartBoundTorsion | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Same canonical data; textual hits: equivalence, lowerStar. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProperOpenCoefficientRefinement | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ProperWContractibleClosedFibreRigidity | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.PurEtaleScalarMateProjection | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.PurIntegralReductionUniformTor | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurIntegralRepresentingPair | B9 | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.PurKFlatOpenModelMaps | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.PurKFlatOpenProjectionModel | A3 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PuritySectionEtaleRestriction | Y2 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.PurityWitnessedOpenChartTransport | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.QcqsConstructibleIntegralLatticeTree | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.QcqsIntegralFiniteModelCompleteness | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.QcqsIntegralScalarExtensionCTF | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.QcqsLatticeTreeReconstruction | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.QcqsLisseStratifiedIntegralLattices | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.QcqsProperConstructibleClosedBaseChange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.QcqsProperSerreHeartBound | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.QlbarBoundedTensorColimit | unclaimed | Same canonical data; textual hits: ring, equivalence, upperStar. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | F6 | Same canonical data; textual hits: ring, equivalence, adjunction. |
| Sheaf.Paper.QuotientPullbackTensorCoherence | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.QuotientSectionTensorNormalization | unclaimed | Same canonical data; textual hits: ring, equivalence, upperStar. |
| Sheaf.Paper.RadicialEtaleRationalUnitRetraction | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same canonical data; textual hits: lowerStar, upperStar, adjunction. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RationalAffineTensorCalculus | J6 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.RationalTatePullback | unclaimed | Same canonical data; textual hits: equivalence, upperStar. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RealizationContinuousDirectImage | unclaimed | Same canonical data; textual hits: ring, lowerStar. |
| Sheaf.Paper.RealizationLocalizedPush | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.RefinementCoefficientMate | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RestrictedCoefficientMateProjection | unclaimed | Same canonical data; textual hits: equivalence, upperStar. |
| Sheaf.Paper.RestrictedCoefficientPullbackData | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RootTowerCoordinateFace | W5 | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RootTowerPunctureInvariance | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.RootTowerPuncturedFaceDiagram | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ScalarChangeDirectImageUnit | unclaimed | Same canonical data; textual hits: equivalence, upperStar, adjunction. |
| Sheaf.Paper.ScalarCompositeMateAdjunct | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ScalarIteratedMatesAdjunct | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ScalarModelImmersionExtension | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ScalarPullbackComposition | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.ScalarPullbackIsoExistence | unclaimed | Same canonical data; textual hits: lowerStar, upperStar, adjunction. |
| Sheaf.Paper.ScalarPullbackIsoUniqueness | unclaimed | Same canonical data; textual hits: upperStar, adjunction. |
| Sheaf.Paper.ScalarPullbackRepresentativeData | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.ScalarReductionTowerBalancing | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ScalarTensorPullbackNormalization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.SectionCompactSourceExchange | H7 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization | unclaimed | Same canonical data; textual hits: ring, equivalence, upperStar. |
| Sheaf.Paper.SectionDerivedPushpullNormalization | unclaimed | Same canonical data; textual hits: equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.SectionDerivedRealization | A8 | Same canonical data; textual hits: equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.SectionDerivedTensorNormalization | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SectionGeometricAdjunctionBridge | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.SectionKFlatTensorComparison | unclaimed | Same canonical data; textual hits: ring, equivalence. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Same canonical data; textual hits: ring, equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.SectionOplaxTotalComparison | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| Sheaf.Paper.SectionOrdinaryOplaxNormalization | unclaimed | Same canonical data; textual hits: ring, equivalence, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.SectionResolutionConjugationIdentities | unclaimed | Same canonical data; textual hits: equivalence, upperStar. |
| Sheaf.Paper.SectionTotalOplaxComparisonData | unclaimed | Same canonical data; textual hits: equivalence, upperStar. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.SfPackageBaseChangeDomainRealization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.SfPackageCommonStageTransport | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.SfProEtaleProjectionFormula | N4 | Same canonical data; textual hits: ring. |
| Sheaf.Paper.SfRationalLocalizationOrthogonality | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | M2 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | Same canonical data; textual hits: equivalence, adjunction. |
| Sheaf.Paper.SmoothPurityReductionDerivedMonoidalTower | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.StratifiedFiniteProjectiveTor | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.StratumPerfectUniformBounds | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.StrictCompletionFiniteConstantModels | unclaimed | Same canonical data; textual hits: ring, equivalence. |
| Sheaf.Paper.StrictCompletionRestrictionComparison | unclaimed | Same canonical data; textual hits: ring, equivalence, upperStar. |
| Sheaf.Paper.StrictCompletionRestrictionData | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| Sheaf.Paper.StrictCompletionRestrictionLimits | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.StrictDirectImageMixedUnit | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.StrictIntegralScalarPullback | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.StrictSectionPrincipalQuotientModels | R5 | Same canonical data; textual hits: ring. |
| Sheaf.Paper.StrictSectionScalarPresentation | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | Same canonical data; textual hits: lowerStar, adjunction. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.SupportedFiniteSubextensionImageComparison | A4 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SupportedImageDerivedCompleteness | C3 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SupportedImageKoszulComparisonNonpositive | G1 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SupportedImageRigidityFromModelComparisons | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SupportedImageTorsionReductionsCd | E1 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Same canonical data; textual hits: ring, lowerStar, upperStar. |
| Sheaf.Paper.SupportedModelHullProetaleDescent | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.SupportedRationalModelRigidityTransfer | M5 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SupportedRootScalarSiteComparison | A7 | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.SupportedThreeTermScalarCd | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SupportedThreeTermScalarRigidity | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.SupportedTriangleMateIdentification | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.SystemBlockRepetition | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.SystemCompactSupportData | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SystemCompactSupportEvaluation | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.SystemEnrichedProjectionAdjunction | unclaimed | Same canonical data; textual hits: lowerStar, upperStar, adjunction. |
| Sheaf.Paper.SystemInternalHomRepresentability | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Same canonical data; textual hits: ring, lowerStar, upperStar, adjunction. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Same canonical data; textual hits: equivalence, adjunction. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.TensorAdjunctionExchange | S1 | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.TensorMateBaseChange | P5 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.TowerAdjointCompositorRealization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.TowerP1UniformCtfDomains | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.TraceStalkCompositorTowerRealization | K9 | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.TransverseTameOpenShriekExchange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | Q1 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.VectorIntegrationSiteComparison | S6 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.VectorModelChartDescent | W7 | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.VectorTraceScalarDescent | S8 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.Paper.WStrictLisseComponentCohomology | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.WeaklyEtaleDerivedEvaluationRestriction | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.WeilCompactStructureTensorComparison | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.WeilFourierTransform | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.Paper.WeilIndProperHigherRepresentability | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.Paper.ZlOpenExtensionTExact | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.PoincareDuality.OpenModuleKFlatProjectionModel | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | N2 | Same canonical data; textual hits: upperStar. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SecSmoothPurity.ReductionExceptional | K5 | Same canonical data; textual hits: lowerStar, upperStar, adjunction. |
| Sheaf.SecSmoothPurity.SupportedScalarTorInterval | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | R4 | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | S1 | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.SixFunctors.DetSfCompBaseChangeDefs | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.EtaleHomComparisonModels | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.EtaleOpenKFlat | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.EtaleOpenTensorDefs | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Same canonical data; textual hits: equivalence, adjunction. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.FiniteCtfInternalEtaleRealization | C6 | Same canonical data; textual hits: lowerStar. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.SixFunctors.FiniteExceptionalDomain | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.FiniteFreeComparisonTransitivity | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.SixFunctors.FiniteFreeImageComparison | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.GeneratorReductionStatement | S2 | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.SixFunctors.IntegralBasicRealization | T1 | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | G2 | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | T2 | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.KunnethFirstOpenSubstitution | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.SixFunctors.NormedInverseImageScalarTransport | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | Same canonical data; textual hits: ring. |
| Sheaf.SixFunctors.OpenFactorCoherence | Y8 | Same canonical data; textual hits: ring. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.OpenScalarConjugateNormalization | unclaimed | Same canonical data; textual hits: ring, equivalence. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Same canonical data; textual hits: ring. |
| Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits | F7 | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.ProductCompactificationIdentity | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Same canonical data; textual hits: equivalence, lowerStar. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | J3 | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.RationalOperations | D2 | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.SixFunctors.RationalVerdier | B6 | Same canonical data; textual hits: equivalence, adjunction. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.ScalarDirectImageMateCoherence | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.ScalarSixCtf | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.SixFunctors.ScalarSixDefinitions | unclaimed | Same canonical data; textual hits: ring, equivalence, lowerStar, upperStar. |
| Sheaf.SixFunctors.ScalarSixDerivedPullbackNormalization | unclaimed | Same canonical data; textual hits: upperStar. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.ScalarSixGeometry | unclaimed | Same canonical data; textual hits: ring, equivalence, lowerStar. |
| Sheaf.SixFunctors.ScalarSixHeartLatticeExtension | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.SixFunctors.ScalarSixImmersionComparison | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.SixFunctors.ScalarSixLisseExtensionConstructible | unclaimed | Same canonical data; textual hits: equivalence, upperStar. |
| Sheaf.SixFunctors.ScalarSixOpenComparison | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same canonical data; textual hits: adjunction. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Same canonical data; textual hits: equivalence. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.Targets.AffineSpaceRationalLine | P2 | Same canonical data; textual hits: upperStar. |
| Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.WeilSheaf.NativeBasicComparisons | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.WeilSheaf.NativeCompactificationModelComparison | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.WeilSheaf.NativeCompatibleTowerCalculation | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.WeilSheaf.NativeDerivedHomComparison | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Same canonical data; textual hits: ring, adjunction. |
| Sheaf.WeilSheaf.NativeImmersionHeartLocalization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.WeilSheaf.NativeInjectiveAdjunctionModel | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.WeilSheaf.NativeOpenProperForgetting | unclaimed | Same canonical data; textual hits: lowerStar. |
| Sheaf.WeilSheaf.NativeOpenProperInterchange | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.WeilSheaf.NativePullbackStarPreservation | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| Sheaf.WeilSheaf.ProperSheafFiniteness | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same canonical data; textual hits: ring, lowerStar, upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.DeligneLaumon.AffineLine.Punctual | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualSupport | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same canonical data; textual hits: ring, lowerStar. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | M3 | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseSheafEquivalence | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSections | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.FiniteStage | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Remarks | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AdicAbIdentification | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedLowerStar | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicHFinite | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafBasis | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeSemilinear | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantBounded | unclaimed | Same canonical data; textual hits: ring, lowerStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarDevissage | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarDevissageRegular | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisse | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisseComponents | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeAdic | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLisse | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsConstructible | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtensionConstructible | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.ProjectionPullback | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormulaBounded | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension | unclaimed | Same canonical data; textual hits: upperStar, adjunction. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Same canonical data; textual hits: lowerStar, upperStar, adjunction. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionCoherence | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Same canonical data; textual hits: adjunction. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjection | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| WeilConjectures.WeilSheaf.ArtinSchreierInertia | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.WeilSheaf.ArtinSchreierIsotypic | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.ArtinSchreierMul | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.ArtinSchreierNeg | unclaimed | Same canonical data; textual hits: ring, lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.ArtinSchreierPullback | unclaimed | Same canonical data; textual hits: ring, lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.WeilSheaf.BaseChangeField.Cohomology | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.BaseChangeField.Comparison | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.BoundaryStalkFrobenius | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.BoundaryStalkSpecialization | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.ClosedLowerStar | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.CohomologyNonneg | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.CohomologyProEtale | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.CompactSupportAdicConstant | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.ConstantTwistWeight | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same canonical data; textual hits: ring, lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.FiniteEtale | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.FiniteLeray | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.FiniteLowerStar | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Same canonical data; textual hits: ring, lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.FourierBaseLinear | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierFirstFormula | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| WeilConjectures.WeilSheaf.FourierInversion.ConvolutionKernel | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierInversion.KernelComposition | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierInversion.Reflection | unclaimed | Same canonical data; textual hits: ring, upperStar. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierStalkFibre | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.GlobalSectionsUpperStar | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.HigherLowerStarZero | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStar | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.Isotypic | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.IsotypicPullback | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.LSeries | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.WeilSheaf.LisseExtension | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.ExtensionByZero | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerShriek | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerStar | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.ProperBaseChange | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Same canonical data; textual hits: lowerStar. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.WeilSheaf.TraceFunction | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.UpperStarLowerStar | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Same canonical data; textual hits: upperStar. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same canonical data; textual hits: ring. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same canonical data; textual hits: lowerStar, upperStar. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same canonical data; textual hits: ring. |

## Status

landed 20261025T100919-L-3638556 2026-10-25 (merge of deliver/D4/Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport)
