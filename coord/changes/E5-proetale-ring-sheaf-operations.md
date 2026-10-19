# AlgebraicGeometry.ProEtale.ringSheaf operations

## Reason

Move the eight existing transparent operations to a common module so that localization and base-change lemmas can import them without importing the theorem that uses those lemmas. The original module publicly re-exports the common module. No binder, universe, type, body, name or visibility changes. No target meaning changes. No consumer adaptations are needed.

## Old

In lean/Sheaf/AlgebraicGeometry/ProEtaleOpenClosedSequenceRingSheaf.lean:

```lean
/-- Module inverse image, with inverse-image coefficients and the transported action.
Source: Stacks, Tags 03D2 and 09A5
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafInverseImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (upperStar Ab.{u + 1} f).mapMod B

/-- Module direct image, with scalars restricted through the canonical ring unit.
Source: Stacks, Tag 03D3 and Pro-etale Cohomology, section 09A5
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafDirectImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (lowerStar Ab.{u + 1} f).mapMod ((upperStar Ab.{u + 1} f).obj B) ⋙
    Mod.comap ((upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom B)

/-- The actual inverse-image/direct-image module adjunction.
Source: Stacks, Tag 03D3
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafAdjunction {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafInverseImage f B ⊣ ringSheafDirectImage f B :=
  (upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction B

/-- Extension by zero with its coefficient action supplied by the existing projection
formula linearization. Its carrier is the sheafification of extension by zero of the
underlying abelian presheaf, and its action is the sheafified original action.
Source: Stacks, Tags 03DI, 03DJ and 09AE
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft B

/-- The extension-by-zero adjunction with its specified underlying abelian unit and counit.
Source: Stacks, Tag 03DI
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafOpenExtension j B ⊣ ringSheafInverseImage j B :=
  (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeftAdjunction

/-- The fixed inverse-image composition comparison on a pullback square.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafSquareComparison {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X) :=
  upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f))

/-- The canonical coefficient identification, with the two successive inverse-image
ring structures made explicit, rather than the structure on a composite functor.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
def ringSheafSquareCoefficient {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    (upperStar Ab.{u + 1} (pullback.fst g f)).obj ((upperStar Ab.{u + 1} g).obj B) ⟶
      (upperStar Ab.{u + 1} (pullback.snd g f)).obj ((upperStar Ab.{u + 1} f).obj B) :=
  (ringSheafSquareComparison g f).hom.app B

/-- Pullback along the fibre projection, with scalars identified by the fixed canonical
composition comparison. Multiplicativity of this comparison is concluded in the theorem.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafSquarePullback {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    [IsMonHom (ringSheafSquareCoefficient g f B)] :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ((upperStar Ab.{u + 1} f).obj B) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (pullback g f)) Ab.{u + 1})
        ((upperStar Ab.{u + 1} (pullback.fst g f)).obj
          ((upperStar Ab.{u + 1} g).obj B)) :=
  ringSheafInverseImage (pullback.snd g f) ((upperStar Ab.{u + 1} f).obj B) ⋙
    Mod.comap (ringSheafSquareCoefficient g f B)
```

## New

In lean/Sheaf/AlgebraicGeometry/ProEtaleRingSheafOperations.lean, re-exported by the old module:

```lean
/-- Module inverse image, with inverse-image coefficients and the transported action.
Source: Stacks, Tags 03D2 and 09A5
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafInverseImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (upperStar Ab.{u + 1} f).mapMod B

/-- Module direct image, with scalars restricted through the canonical ring unit.
Source: Stacks, Tag 03D3 and Pro-etale Cohomology, section 09A5
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafDirectImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (lowerStar Ab.{u + 1} f).mapMod ((upperStar Ab.{u + 1} f).obj B) ⋙
    Mod.comap ((upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom B)

/-- The actual inverse-image/direct-image module adjunction.
Source: Stacks, Tag 03D3
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafAdjunction {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafInverseImage f B ⊣ ringSheafDirectImage f B :=
  (upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction B

/-- Extension by zero with its coefficient action supplied by the existing projection
formula linearization. Its carrier is the sheafification of extension by zero of the
underlying abelian presheaf, and its action is the sheafified original action.
Source: Stacks, Tags 03DI, 03DJ and 09AE
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft B

/-- The extension-by-zero adjunction with its specified underlying abelian unit and counit.
Source: Stacks, Tag 03DI
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafOpenExtension j B ⊣ ringSheafInverseImage j B :=
  (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeftAdjunction

/-- The fixed inverse-image composition comparison on a pullback square.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafSquareComparison {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X) :=
  upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f))

/-- The canonical coefficient identification, with the two successive inverse-image
ring structures made explicit, rather than the structure on a composite functor.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
def ringSheafSquareCoefficient {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    (upperStar Ab.{u + 1} (pullback.fst g f)).obj ((upperStar Ab.{u + 1} g).obj B) ⟶
      (upperStar Ab.{u + 1} (pullback.snd g f)).obj ((upperStar Ab.{u + 1} f).obj B) :=
  (ringSheafSquareComparison g f).hom.app B

/-- Pullback along the fibre projection, with scalars identified by the fixed canonical
composition comparison. Multiplicativity of this comparison is concluded in the theorem.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafSquarePullback {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    [IsMonHom (ringSheafSquareCoefficient g f B)] :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ((upperStar Ab.{u + 1} f).obj B) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (pullback g f)) Ab.{u + 1})
        ((upperStar Ab.{u + 1} (pullback.fst g f)).obj
          ((upperStar Ab.{u + 1} g).obj B)) :=
  ringSheafInverseImage (pullback.snd g f) ((upperStar Ab.{u + 1} f).obj B) ⋙
    Mod.comap (ringSheafSquareCoefficient g f B)
```

## Users

The downstream.py inspection covers all eight moved names. The current direct importers
are listed below, including the three modules that refer to the moved operations by name.
The other direct importers use the theorem or its public imports. The complete transitive
closure inherits the same public declarations: all eight definition blocks and the parent
theorem signature are textually identical to the current originals. No target meaning
changes, no module requires source adaptation, and no held module is edited.

The following table includes the complete downstream.py transitive closure, not only
name-mentioning consumers. Since the public API and definition bodies are unchanged,
every row has the same effect; no consumer source is part of this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | D3 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | E3 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | A9 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | G3 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence | J5 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle | T9 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts | V7 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedReconstruction | K1 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedProductQuotientModel | unclaimed | Same public API; no adaptation. |
| Sheaf.CategoryTheory.LocalizationInverseImageCoherence | C1 | Same public API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same public API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same public API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same public API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same public API; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicClosedConstructible | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Same public API; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | Same public API; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | Same public API; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | H5 | Same public API; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Same public API; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Same public API; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Same public API; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | Same public API; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | E4 | Same public API; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | U5 | Same public API; no adaptation. |
| Sheaf.Paper.CoefficientHeart | X8 | Same public API; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | P4 | Same public API; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | P7 | Same public API; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Same public API; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Same public API; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Same public API; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CondensedERealization | Y9 | Same public API; no adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | U7 | Same public API; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | Same public API; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | Z7 | Same public API; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | U8 | Same public API; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | P8 | Same public API; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | C5 | Same public API; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | G3 | Same public API; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | S1 | Same public API; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Same public API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Same public API; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Same public API; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Same public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | G7 | Same public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | U3 | Same public API; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Same public API; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteTorInternalHomAnyField | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteWindow | W5 | Same public API; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | C1 | Same public API; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | Same public API; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | Q9 | Same public API; no adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | W5 | Same public API; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | M2 | Same public API; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | W6 | Same public API; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | K4 | Same public API; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | M1 | Same public API; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | W8 | Same public API; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | M2 | Same public API; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | E9 | Same public API; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | E7 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | J9 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.IntegralExtensionByZero | A3 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralModels | D4 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | K1 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | Y9 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | N3 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | J2 | Same public API; no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | F2 | Same public API; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Same public API; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Same public API; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Same public API; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Same public API; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Same public API; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Same public API; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | Same public API; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Same public API; no adaptation. |
| Sheaf.Paper.ProperHeartBound | K5 | Same public API; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | Y5 | Same public API; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Same public API; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Same public API; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Same public API; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Same public API; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.QbarOrdinaryAdjunction | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | C1 | Same public API; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Same public API; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Same public API; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Same public API; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Same public API; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SfPreservationClass | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | Same public API; no adaptation. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | Same public API; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TateInverseLimitBaseChange | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Same public API; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Same public API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | X9 | Same public API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | K4 | Same public API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | E3 | Same public API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | Same public API; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same public API; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Same public API; no adaptation. |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | N1 | Same public API; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.FiniteCompactProetale | A2 | Same public API; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.FlatModel | A3 | Same public API; no adaptation. |
| Sheaf.SixFunctors.FlatModelGeneration | S3 | Same public API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | Same public API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | B8 | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | T4 | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Same public API; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.ScalarSixPullback | U6 | Same public API; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same public API; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | Same public API; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same public API; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Same public API; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same public API; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same public API; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Same public API; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Same public API; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same public API; no adaptation. |
| TargetsCheck | unclaimed | Same public API; no adaptation. |
| WeilConjectures | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Same public API; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same public API; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same public API; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Same public API; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same public API; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same public API; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same public API; no adaptation. |

## Status

landed 20261019T093345-L-2300588 2026-10-19 (merge of deliver/E5/Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf)
