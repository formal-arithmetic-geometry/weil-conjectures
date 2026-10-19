# AlgebraicGeometry.Etale.SupportedDerivedScalarUnit

## Reason

The irreducible universal-property definition caused a kernel deterministic timeout even when
proving its unfolding equation by reflexivity (TransportAPIOct20 diagnostic: 10,000 heartbeats,
11.9 seconds in kernel type checking). The complete item exceeded the 60-second file limit.
Name the canonical derived unit map, state its universal property as a one-field Prop
structure for an arbitrary exact functor, and specialize that predicate to scalar restriction.
Proofs use its constructor and projection and prove categorical glue with abstract instances,
without repeatedly unfolding the large concrete derived-category expressions.
The structure has exactly the old hypotheses and exactly the old universal property, for
all unbounded derived objects, with the same normalized unit and no flatness assumption.
There is no arbitrary data, new axiom or new sorry.

OrdinarySupportedKummerScalar is unclaimed (coord/claims checked before editing); the assigned
item is held by M4. The item also caches small-etale weak sheafification in private local
instances, reducing its coefficient-unit identification to a six-second diagnostic compile.

## Old

```lean
@[irreducible]
def SupportedDerivedScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) : Prop :=
  ∀ K : DerivedCategoryModule S T,
    Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj G ⟶ K ↦
      (DerivedCategory.singleFunctor _ 0).map η ≫
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).inv.app
          G ≫
          (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategory.map f)
```

## New

```lean
/-- The normalized degree-zero map associated with an ordinary coefficient unit.
Source: Stacks 07A6 (blueprint: def-asd-ordinary-supported-kummer-scalar). -/
def exactDerivedScalarUnitMap
    {C : Type u₁} [Category.{v₁} C] [CategoryTheory.Abelian C]
    [HasDerivedCategory.{w₁} C]
    {B : Type u₂} [Category.{v₂} B] [CategoryTheory.Abelian B]
    [HasDerivedCategory.{w₂} B]
    (V : B ⥤ C) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {F : C} {G : B} (η : F ⟶ V.obj G) :
    (DerivedCategory.singleFunctor C 0).obj F ⟶
      V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor B 0).obj G) :=
  (DerivedCategory.singleFunctor C 0).map η ≫
    (V.mapDerivedCategorySingleFunctor 0).inv.app G

/-- The degree-zero scalar-unit property for an exact functor between abelian categories.
This keeps the chosen derived-category structures abstract during construction.
Source: Stacks 07A6 (blueprint: def-asd-ordinary-supported-kummer-scalar). -/
structure ExactDerivedScalarUnit
    {C : Type u₁} [Category.{v₁} C] [CategoryTheory.Abelian C]
    [HasDerivedCategory.{w₁} C]
    {B : Type u₂} [Category.{v₂} B] [CategoryTheory.Abelian B]
    [HasDerivedCategory.{w₂} B]
    (V : B ⥤ C) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (F : C) (G : B) (η : F ⟶ V.obj G) : Prop where
  /-- The derived unit represents maps to every restricted derived object. -/
  bijective (K : DerivedCategory B) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor B 0).obj G ⟶ K ↦
      exactDerivedScalarUnitMap V η ≫ V.mapDerivedCategory.map f)

/-- The universal-property formulation of a derived scalar-extension unit at F.
The target is G in degree zero, while test objects K range over the entire unbounded
derived category. This is derived tensor extension, with no flatness assumption on S.
Source: Stacks 07A6 (blueprint: def-asd-ordinary-supported-kummer-scalar). -/
abbrev SupportedDerivedScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) : Prop :=
  ExactDerivedScalarUnit (Sheaf.restrictScalars T.smallEtaleTopology φ) F G η
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar --uses
SupportedDerivedScalarUnit` found two modules with term-level occurrences: the defining
module and the assigned item. All other source occurrences are a documentation reference.
The full original transitive import closure and the new GeoCartierCoeffExtension
user of the generic map are listed below for review. No target signature is
edited. Any target meaning check involving the changed predicate is reopened for the
independent reader to confirm that packaging one proposition in a structure preserves it.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed | New user of exactDerivedScalarUnitMap; definition factoring recorded separately in M4-supported-coefficient-derived-unit-map.md. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | T3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | G6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | G1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | K8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | F6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | M3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.Curve.SepclosedRegularProperTrace | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | D3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | D2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.FiniteFlatRegularDivisorPurityDescent | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.FormalPuncturedSections | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | P9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.KummerRootRegularDivisorPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.KunnethSupported | X3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.NoetherianAffineLineUnit | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | S8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | C7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | B5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | T8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | X7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.PunctualPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.PunctualPurityEtaleLocality | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.PunctualPurityProperDegreeDescent | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.PunctualPurityTraitTest | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.PunctualPurityTwoOfThree | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.PunctualStrictCompletionTest | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.PuncturedPerverseHighComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.PuncturedSupportCohomologicalBound | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | S1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.SemistableCoordinateDivisorPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | K1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | P5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.StrictLocalEtaleDimensionBounds | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | A3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | S2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | K4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarSource | M4 | Updated proof uses constructor and bijective projection. |
| Sheaf.AlgebraicGeometry.TransverseGysinLimit | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | F7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.VectorExtensionSplittingCohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | F9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicCompactificationSectionRealization | B8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | C7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | C8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicSectionClosedSupport | Y5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.BoundaryDualizingComposition | Q8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | Q9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | R5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.BrownExceptionalAdjoint | G3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CartesianCoefficientTwists | Z6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CartesianCoefficients | E8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CartierClassAgreement | U5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ChernFlagFormula | G4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ClosedSupportConstructible | A7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CoefTowerCoaugmentation | R3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | F3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CoefficientHeart | X8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CoefficientHeartFiltration | P4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | K6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | Y2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CommonStageWeilShriek | R7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactFiberStalk | E7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | G7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactSupportCondensedRealization | U3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactSupportFiniteAction | K4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | R6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactSupportPerfectness | Q4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactSupportReductionTower | P2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | R9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactificationLocalizing | F4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | Y9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompletedTensorHomTranspose | D2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CompletionSupportedConstantComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConnectedConstantH0 | W3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | J4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | R2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConstructibleHomComparison | H1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | R2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | E6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | T2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DiagonalTowerLimit | S9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DiagonalTowerSystem | W6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DirectImageChangeRingTranspose | J2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | R2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.EtaleGeometricBiduality | G1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | U4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | Z5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ExceptionalFiniteRealization | Z6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | D6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ExceptionalProEtaleRealization | Q3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FieldShriekCompositionQcqs | P8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FieldShriekLowerBound | F1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FieldWeilShriekShiftData | G1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | C2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteClosedShriek | K6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteCoefficientHomChange | M1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | G9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteConstructibleHom | M4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteEtaleDescent | U1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteFieldExceptionalPreservation | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | N3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteProperLocalizing | W7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteResidueDualizing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteRingSectionDeformation | G9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteStageVerdierBiduality | N4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | Y6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteTateSiteDescent | V9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteWindow | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | X3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | V8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | A5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | D9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | X2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | W7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | W5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralConstantModelHeart | G2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralConstructibleHeart | P1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralConstructibleInternalHom | P1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | S4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralExceptionalInverseImage | M3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralHeartDualizable | C5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralHeartLocalModel | C3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralModels | D4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralModelsOperations | N1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | Y8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralProperProjectionFormula | V4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralStratumExtBound | C2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralStratumHomFormula | Y9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralTensorProduct | N3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralTensorPullback | J2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralTwistBaseChange | J4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralTwistScalarCoherence | N4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.InterchangeProperPasting | S4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.InternalHomPullback | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IteratedWeilCocycle | D4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.KummerAdditivity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.LocalFrobeniusConjugacy | Q5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | A6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.LocalizedTopChern | E5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.MateOpenRestriction | U2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.MiddleExtensionHcZero | E5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | W5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | T8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PointCompletedEvaluation | E4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | D2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperCoincidenceFrobenius | T6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperCompactCoincidence | P9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperHeartBound | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperHeartBoundLattice | Y5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperHeartBoundReduction | V4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | T7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PuncturedDerivedCompletionSections | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurAdicReconstruction | H8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | Y2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityConventions | X8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityCoprojection | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | R3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | R2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityDivisorClass | J7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityDncComparisons | G3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityFiniteKummerLevel | P1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityFrameClass | K6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityFrameIndependence | A4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityGysinStructure | F1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityRankOneLocalCalculation | F2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityRelativeKummer | F4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PuritySourceTransports | V6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | H9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.QcqsCompactSupportRealization | D3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RationalRestrictionGlue | Z9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RationalStalkExact | A7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.RestrictionLocal | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | F9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SfBidualityClass | C6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | K9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | T3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SmoothPurityMap | R2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | C1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SmoothPurityTowerBound | J3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | M4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SmoothTrace | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.StratifiedLatticeRank | T9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedCupFunctoriality | E4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedHomPullback | H4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SystemClopenTensorCompatibility | Y5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | F5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.SystemOperationExchangeRealization | K1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TateTwistLocallyFree | S7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TowerClassChern | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TowerClassFinite | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TowerClassProjective | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TowerClassPullback | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TowerClassReduction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TowerClassSystems | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | N2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceBaseChangeFirst | E1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceCompactificationCohomology | U5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TrfDevissageGeneration | C2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TrfWitnessedOpenPullback | J8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TwConventions | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.TwistPreservesFiniteness | G5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.UniformConstructibleExtIntegral | Z9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.UniformConstructibleExtRational | X8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.VaryingRingGraphSummand | B2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.VectorBundlePurity | S1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.VerdierExchange | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.WeilCompactSupportCohomology | A8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.WeilFourierInversion | J6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.WeilOne | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.WeilOpenImageDelta | E7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | S2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.WfTensorCompletionFrobenius | U8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ZlFrameworkOpenExchange | Q8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | P7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | J7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | U2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.RingTheory.CompleteLocalConnectednessBound | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.RingTheory.NormalPuncturedHypersurfaceConnected | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | W9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | U8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | U9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | M9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | G1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | N2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | M1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | V1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Z9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | J5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.CompactCoefficientComposition | U6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.CompositionProjectionMate | V5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | P6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.FieldTensor | G2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | W2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.FiniteDualizing | M6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | M7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.GeneratorReductionStatement | N3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | B5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | M2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | Z8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | W8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | P5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | A8 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralOperationShiftData | R1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | T9 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | R5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.OpenAdjunctionShift | J1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.OpenFactorCoherence | M2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | F4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | K2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | X5 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.RationalVerdier | V4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | E4 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | S6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | D6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | H1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.Targets.VectorBundlePurity | F6 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | Y7 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | H1 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | T2 | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| TargetsCheck | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.Statement | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No term-level use of the predicate; imported propositions retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar | unclaimed | Proposition encoded by its one-field structure; same universal property; no holes. |

## Status

landed 20261019T231236-L-565115 2026-10-19 (merge of deliver/M4/Sheaf.AlgebraicGeometry.SupportedKummerScalarSource)
