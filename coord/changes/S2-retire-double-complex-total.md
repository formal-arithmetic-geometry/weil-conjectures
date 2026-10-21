# HomologicalComplex₂.firstFiltration and HomologicalComplex₂.secondFiltration

## Reason

This is the zero-hole duplicate-retirement assignment in coord/retire-items.tsv,
retire:Sheaf.CategoryTheory.DoubleComplexTotal. The adopted source twin already
proves every theorem in this module. Both files introduce the same constant names,
so retaining the copy prevents environments from loading both families of consumers.
The source twin packages its finite-supremum filtrations with PBCDecreasingFiltration;
the Sheaf copy uses the canonical DecreasingFiltration. Consumers use the step
subobjects, not either filtration structure as an argument of a generic operation.
Retire the duplicate, redirect every active direct importer and preserve the canonical
compatibility API with explicit CanonicalFiltration imports.

Source: Stacks Project, Homological Algebra, Section 12.18 (Tag 012Z), and current
blueprint main-20261015, def-sp-double-complex-total. No target statement changes.

## Old

The withdrawn module publicly imports WeilConjectures.CategoryTheory.CanonicalFiltration.
Its two construction bodies, verbatim:

```lean
noncomputable def firstFiltration (n : ℤ) :
    DecreasingFiltration ((K.total (ComplexShape.up ℤ)).X n) where
  F p := (Finset.Icc p n).sup
    (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n))
  F_succ_le p := K.firstFiltration_antitone n (by omega)

noncomputable def secondFiltration (n : ℤ) :
    DecreasingFiltration ((K.total (ComplexShape.up ℤ)).X n) where
  F p := (Finset.Icc p n).sup
    (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n))
  F_succ_le p := K.secondFiltration_antitone n (by omega)
```

The other declarations have the same names, hypotheses, and proof bodies as their
adopted-source counterparts, apart from the private graded_differential helper's
parameter type (DecreasingFiltration here, PBCDecreasingFiltration upstream).

## New

The module is withdrawn via deleted.txt. Its 16 active direct consumers replace
Sheaf.CategoryTheory.DoubleComplexTotal by WeilConjectures.CategoryTheory.DoubleComplexTotal,
preserving public versus proof-only import visibility (including import all).
Each consumer that re-exported the old module (public import) also publicly imports
WeilConjectures.CategoryTheory.CanonicalFiltration, preserving for its importers the
old module's public compatibility declarations. The five proof-only consumers
(FilteredInjectiveResolution, SourceHyperExtModuleTarget, AcyclicCoproductExtOrthogonalHom,
BoundedBelowCechConeComparison, QcoherentNormalizedPullbackSquare) compile without it and
do not add it (reviewer correction, 2026-10-21).
No declaration text, proof, attribute or declaration visibility changes in a consumer.
Current main already uses the adopted source naturality API and provides the
comparison component/naturality lemmas used by its restored consumers. The older
sandbox comparison and effacement optimizations are omitted on rebase: no
comparison definition, helper, theorem or node is changed by this delivery.
The restored QcoherentNormalizedPullbackSquare receives the import migration;
the restored QcoherentNormalizedComparison and CoherentFrobeniusPullback already
use current main's compatible imports and are unchanged.
The upstream definition bodies are preserved verbatim:

```lean
noncomputable def firstFiltration (n : ℤ) :
    PBCDecreasingFiltration ((K.total (ComplexShape.up ℤ)).X n) where
  step p := (Finset.Icc p n).sup
    (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n))
  antitone_step := K.firstFiltration_antitone n

noncomputable def secondFiltration (n : ℤ) :
    PBCDecreasingFiltration ((K.total (ComplexShape.up ℤ)).X n) where
  step p := (Finset.Icc p n).sup
    (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n))
  antitone_step := K.secondFiltration_antitone n
```

The step values are definitionally the same finite supremum in both representations.
The graded pieces are definitionally the same cokernel of Subobject.ofLE of successive
steps; its inequality proofs are equal by proof irrelevance. A scratch compatibility
audit reconstructed the two old definitions and checked by rfl both step equalities
and both graded-piece equalities for arbitrary integer n and p. It compiles in 1.3 s.
This includes empty intervals (p>n), negative total degrees and negative filtration
indices, without imposing a new boundedness or first-quadrant hypothesis.
The first-quadrant theorems retain exactly the original hypotheses and signs.
All 14 public constructions/theorems in the source were checked with #print axioms:
only propext, Classical.choice and Quot.sound occur. The source file is untouched.

The DAG attachment for def-sp-double-complex-total now points at the source twin,
with the exact PBCDecreasingFiltration return type and an explanation of the
representation change. Its mathematical statement, dependency edges, proof plan and
unit route remain unchanged. No target meaning changes, so target review is not reopened.

## Users

The table preserves the prior source-closure inventory and includes current
active consumers, textual users and previously archived consumers. There are
16 current direct importers, all migrated with import-only changes. The restored
normalized pullback-square consumer is included. The restored normalized comparison
and Frobenius pullback already use compatible source imports and are unchanged.
The new degree-zero comparison consumer and the indirect smooth-curve consumer
are explicitly listed. Current main's comparison definitions and proved API stay
verbatim; earlier sandbox optimization changes are omitted on rebase.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Algebra.Homology.FilteredInjectiveResolution | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Algebra.Homology.RingedSiteTorFlatModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Algebra.Homology.SitePerfectLowerModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Algebra.Homology.SitePerfectTorWindow | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Algebra.Homology.SitePerfectUpperModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Algebra.Homology.SourceHyperExtModuleTarget | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineLinearActionRigidity | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineLinearTraceAction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineLinearUniversalAction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | M4 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineTraceLineLocalization | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineTraceLinePurity | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.BoundedComplexDirectImagePresheaf | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.CartesianOpenFiniteStageHypercohomologyModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.CartierDerivedRealization | unclaimed | Transitive consumer: same step and graded-piece values; no declaration edit. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules | C1 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CoefficientTorFlatModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CoherentPowerComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonFlatPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonModuleExact | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | F9 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleLocalDualInterval | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | N3 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ExceptionalBaseChangeCartesianOpenInjectiveAcyclic | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence | N4 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | G5 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteProetaleSmoothBaseChange | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | W3 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GeometricSpecializationCategory | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence | P1 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.MultipointedCurveModification | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | B2 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A6 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ProEtaleAbelianHypercoverAugmentation | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleAbelianHypercoverQuasiIso | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleAbelianHypercoverRowComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleAbelianHypercoverTotal | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverAugmentation | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverInjectiveComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverInjectiveRow | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverQuasiIso | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverTotal | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | unclaimed | Transitive consumer: same step and graded-piece values; no declaration edit. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed | Transitive consumer: same step and graded-piece values; no declaration edit. |
| Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | A7 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ProperHeartContinuityDirectImage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.QcoherentComparisonDegreeZero | unclaimed | Unchanged consumer; the current universe-transport and module-comparison component API is preserved. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison | unclaimed | Restored and proved on current main; source imports and declarations unchanged. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare | unclaimed | Restored on current main; total-complex import migration only; existing source naturality API unchanged. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.SemistableMultipointedPair | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.SfEtaleExchanges | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.SfFullcdUsedClass | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | unclaimed | Same comparison values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | F1 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.AcyclicCoproductExtOrthogonalHom | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.CategoryTheory.BoundedBelowCechConeComparison | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.CategoryTheory.CartanEilenbergAcyclicAbutment | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergDecalageInjectiveModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergDecalageTruncationDiagram | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy | unclaimed | Current main already has compatible imports; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopyComponents | unclaimed | Current main already has compatible imports; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopyFiltration | unclaimed | Current main already has compatible imports; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergFilteredTotalLifts | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergFunctorial | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.CategoryTheory.CartanEilenbergGoodCutDecalage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergGoodCutIdentification | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergHorizontalCutComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergProperties | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.CategoryTheory.CartanEilenbergSecondImageTruncation | unclaimed | Current main already has compatible imports; no source adaptation required. |
| Sheaf.CategoryTheory.CoefficientFiniteLocalSystemsPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.CategoryTheory.ContinuousCocontinuousDerivedShriek | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.DerivedCategory.BoundedBelowSectionModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.DerivedColimitBar | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.DoubleComplexFirstFiltrationDifferential | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.CategoryTheory.DoubleComplexFirstFiltrationMap | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.CategoryTheory.DoubleComplexTotal | S2 | Retired; node points at proved source realization. |
| Sheaf.CategoryTheory.DoubleComplexTruncationDecalage | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.GoodTruncationTotalBoundaryImage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.GoodTruncationTotalDecalage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.GoodTruncationTotalImage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.RingedCechCompletionHomInjective | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.RingedCechCompletionRestriction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.RingedCechKoszulDualLimit | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.RingedKoszulCompletionReflector | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.RingedSiteCechRefinementSquare | unclaimed | Current main already has compatible imports; no source adaptation required. |
| Sheaf.CategoryTheory.SecondFiltrationTwoColumnImage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.SiteAugmentationSpectralSequence | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.CategoryTheory.SiteCechEdgeNormalization | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.CategoryTheory.SiteTorIntervalRestriction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.Sites.CoherentConservativeReflection | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.Sites.CoherentObjectApproximation | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.Sites.CoherentToposRepair | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.SmartTruncationDecalageTower | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | U3 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.AdicCoefficientDatumCompleted | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicConstructibleFiniteReductions | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicReductionCohomologySequence | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.AdicResidueLissePerfectLift | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicStratifiedPerfect | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicSuppliedModelFlatCriterion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicTorFlatCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdicTorFlatCriterion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AdmissibleLattices | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AlgebraicallyClosedCoefficients | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AmbientCompleteRawSystem | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BoundedBelowCtfReflection | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BoundedConstructibleComplete | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | E2 | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint | R6 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientExtensionReductionModel | Z9 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientFiniteDescentSections | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientSystemDerivedComparison | V5 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStageCalculus | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStageLisse | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStageLocallyFree | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ComparisonTorAmplitude | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompleteProetale | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompleteResidueCohomologyBounds | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedCoefficientPresentationTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedConstantAlgebraFlatQuotients | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedConstantConstructibility | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedConstantFiniteComplexRealization | Y2 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedConstantSheafReduction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedDirectImageLimits | S9 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedExchangeCoherence | S9 | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedExtensionZeroComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedKoszulQuotientComparison | E4 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedMapReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedOpenExchangeTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedProjectionCoherence | V1 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedPullback | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedPullbackAdjunction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedPullbackReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedPullbackTensorComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedPullbackTriangles | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedPullbackUnitTower | D8 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedScalarShift | F3 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedTensorScalarLinearity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedTowerCorners | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedTowerDirectImage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletedTowerPullback | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CompletionMateComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CondensedAmbientExchange | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedCompactSupportProjection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedERealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedFiniteFreeDerivedHom | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CondensedFiniteFreeHomContinuity | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CondensedFiniteFreeHomEvaluation | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedHypercoverComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CondensedHypercoverInjectiveRow | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CondensedInternalHomSections | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedPointSupertrace | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CondensedQcqsPushforwardLocalComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CondensedUnderivedPushforwardContinuity | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstantCoefficientObjectsConstructible | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstantCompletionEquivalence | V6 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ConstantDirectImagePreservesComplete | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstantInverseImageSection | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ConstantPullbackScalar | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ConstantScalarDirectImageCompleteness | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleCoefficientHomologyTriangulated | A3 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleHeart | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ConstructibleStandardTStructure | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CtfHomConditionB | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CtfHomLocalizationDevissage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CurveMiddleExtension | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DerivedNakayama | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DerivedPullbackTensorHom | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DerivedPullbackTensorIso | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DirectImageCtfOpenTor | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DirectedGaloisFiniteTensorGenerators | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ECoefficientSmoothBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleCENormalizedRowPresentations | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.EtaleCETotalizeAugmentedComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleIntegralLineReductions | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.EtaleIsoDescent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleLocalMonodromyRealization | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.EtaleLocalMonodromyRealizationBase | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.EtaleTermwiseHypercohomology | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ExactPullbackDerivedAdjunction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ExceptionalCoefficientComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ExtendedCechCompletionModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FdCoefficientComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FdPullbackComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteCoefficientDirectImage | C4 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteCoefficientPoint | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteComparisonLocalizing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteExtensionReductionConeBound | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | V8 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteLevelProEtaleBaseChange | B5 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteLevelRectangle | Q4 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteLevelRingedProEtaleBaseChange | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteOrderedFlasqueCechComparison | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.Paper.FinitePerfectAdicRealization | B3 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteProjectiveTensorProducts | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FinitePullbackTensorComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteReductionConstructibility | R1 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteReductionReconstructionCompleted | A2 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteStagePairCategory | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteWindow | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FlatRingedIdealCompleteEquivalence | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FourArrows | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.FourierAdicArtinSchreier | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.FunctorialRingComplexCechComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.GeneralNearbySliceTest | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.GeometricStalkPerfect | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IdentificationFibreAdjunction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralCanonicalTruncations | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralCoherenceTower | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralConstructibleLinear | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralConstructibleTriangulated | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralCriterionReductions | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralCtfTriangulated | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralDerivedCoefficientData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralHeartLocalModel | C2 | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralHomReduction | M4 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralLineTensorComparison | H7 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralLineTensorCompleteness | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralModels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | T5 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralOperationsScalarExtension | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralScalarExtension | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralScalarExtensionConstructible | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralScalarExtensionUniverses | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralTStructure | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntegralUniformCoefficient | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IntrinsicCompletion | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntrinsicCompletionCompleted | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.IntrinsicQbarCategory | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.InverseImagePullbackComparisonDerived | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.KoszulReconstruction | W6 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LevelwiseAdicTruncations | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.LisseCompletedSystemComparison | B6 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LisseNormalizedTowerLocalModels | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LocalizedTStructure | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ModificationsZariskiRefinement | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.NearbyClosedImage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.NearbySpecializationSlice | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.NearbySpreadOut | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.NormalCompletedIntegralModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.NormalizedDVREffectivity | T6 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.NormalizedMonodromyFunctor | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.OrgogozoInductionData | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedClosedBaseRestriction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedConstructibleSetSheaf | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedConstructibleSheaf | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedConstructibleSheafVanishing | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedHypercoverDescentDatum | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedMaximalPointFiniteness | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedNearbyCycles | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedProductPointsConservative | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedProperFibreExchange | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.OrientedSourceLocalization | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcActualRingedExchange | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PbcActualScalarPullback | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PbcActualStrictPullback | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PbcAutomorphismTransport | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcCommonStageCones | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcCompletedPullbackActual | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PbcConeIndependence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcConstructibleReductionCriterion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcConstructibleReductionPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcDescentFunctors | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcExactCompletionData | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PbcFilteredRetractDescent | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PbcFiniteCompletedCoefficientMap | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PbcFinitePullbackConstructibility | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PbcFiniteRawScalarComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcFiniteStageKaroubian | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcIdempotentCompleteTriangulation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcIntrinsicTowerComplete | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcQbarCategory | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcQbarCompletedPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcQbarIdempotentComplete | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcRationalCategory | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PbcRationalTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcScalarExtension | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcSupportCondition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcUniformCompleteTriangulated | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcUniformLocalModelCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcUniformReductionCriterion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcUniformReductionProfile | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PbcVerdierAxioms | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PbcWeilCategory | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PerfectProjectionFormula | T7 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointDerivedHomEvaluation | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointFibreDerivedTensorBasic | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointFibreEquivalence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointReductionUnitNormalization | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PointReductionUnits | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PointSectionsDerivedReduction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PointSectionsFiniteReduction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PointSectionsFiniteness | P3 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PointSectionsScalarExtension | G2 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PointSectionsTensorShift | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PrimeFieldTensorDevissage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ProEtaleConstantReductionTower | G4 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProjectionFormulaBaseChangeNaturality | W8 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProjectionFormulaIdentityCompactification | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperBaseChangeFourArrows | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ProperBaseChangeFourCorners | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperHeartBoundTorsion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperOpenCoefficientMate | V3 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ProperOpenCoefficientRefinement | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurAdicScalarExtensionTorBound | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurEtaleScalarMateProjection | R3 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurTwistSheafLocallyFree | W9 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityConventions | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.QbarIdempotentComplete | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RationalizationIdempotentComplete | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.RationalizationKaroubi | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.RealSheafSections | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RefinementCoefficientMate | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ResidueLissePerfectLift | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ResidueLisseProjectiveModels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.RingComplexFunctorial | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.RingComplexGodementCech | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.RingedPushforwardCompletion | X5 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.SbcCompletedOperations | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ScalarExtensionComposition | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ScalarExtensionExact | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.ScalarExtensionExactIntrinsic | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ScalarPullbackComposition | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.SectionDerivedRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SequentialDerivedInverseLimitCompleted | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfConstructibleHeart | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfExchanges | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfIntegralConstructibleLinear | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfIntegralConstructibleTriangulated | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfIntegralStandardTruncations | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfRationalBoundedConeTorsion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.SfRationalizationKaroubi | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfScalarExtensionComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SfWeilSheafComplex | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SignedLineTensorEquivalence | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SitePerfectComplex | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothExceptionalPreservation | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.SmoothLisseIntegralLattice | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.StratifiedLattice | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.StratifiedOrientedCover | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | J3 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerClassChern | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TowerPreservation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TwConventions | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.UniformCompleteTriangulated | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WContractibleCondensedScalarEvaluation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WContractibleConstantReductionsML | V4 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WeilCompletedCechComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.WeilCompletedKoszulLimitComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.WeilCompletedKoszulProductComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.WeilCompletedKoszulRepresentativeComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.WeilCompletedKoszulRoosComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.WeilCompletedTensorReflector | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.WeilComplexQbarIdempotentComplete | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.WeilTensorProduct | J4 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.RingTheory.CotangentBootstrap | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.RingTheory.CotangentTransitivityTriangle | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.RingTheory.EtaleCotangentVanishing | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.DirectImageScalarExchange | X7 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension | K1 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.AdmissibleDirectImage | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ClosedCostalkDuality | C7 | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FlatModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FlatModelGeneration | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.ScalarSixPullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.TraceFormula.ClosedImageGenericAlteration | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ContractedComponentNoExtraGeneric | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.CurveP1TreeLocalCriterion | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.FinitarySiteCoherentGenerators | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.FiniteBaseCechHypercohomology | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.FiniteEtaModificationGluing | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.TraceFormula.LocalMarkingLength | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.NodalContractionNormalizationBranches | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.OrientedPointCohomology | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.OrientedPointNormalizedStratum | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.TraceFormula.ProjectiveLineTree | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ProperBaseChangeCoherentConservative | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.SemistableMarkedPoint | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.SimplicialDerivedImageSpectralSequence | unclaimed | Migrate retired import; retain canonical filtration API; declarations unchanged. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ValuationReducedFibreNormalization | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Same step subobjects and theorem API transitively; no source adaptation required. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| TargetsCheck | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.Algebra.Homology.ConeHorizontalStepStable | unclaimed | Adopted source API; untouched. |
| WeilConjectures.Algebra.Homology.FiniteStripConeFiltration | unclaimed | Adopted source API; untouched. |
| WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparisonFinite | unclaimed | Adopted source API; untouched. |
| WeilConjectures.AlgebraicGeometry.EtaleCENormalizedRowPresentations | unclaimed | Adopted source API; untouched. |
| WeilConjectures.AlgebraicGeometry.EtaleCERowCyclesNaturality | unclaimed | Adopted source API; untouched. |
| WeilConjectures.AlgebraicGeometry.EtaleCETotalizeAugmentedComparison | unclaimed | Adopted source API; untouched. |
| WeilConjectures.AlgebraicGeometry.EtaleRestrictedSectionsComponentIso | unclaimed | Adopted source API; untouched. |
| WeilConjectures.AlgebraicGeometry.EtaleRestrictedSectionsFactors | unclaimed | Adopted source API; untouched. |
| WeilConjectures.AlgebraicGeometry.EtaleTermwiseHypercohomology | unclaimed | Adopted source API; untouched. |
| WeilConjectures.CategoryTheory.BoundedBelowSecondFiltration | unclaimed | Adopted source API; untouched. |
| WeilConjectures.CategoryTheory.CartanEilenbergRowPages | unclaimed | Adopted source API; untouched. |
| WeilConjectures.CategoryTheory.CartanEilenbergSecondFiltration | unclaimed | Adopted source API; untouched. |
| WeilConjectures.CategoryTheory.DoubleComplexTotal | unclaimed | Adopted source API; untouched. |
| WeilConjectures.CategoryTheory.HypercohomologyFirstPage | unclaimed | Adopted source API; untouched. |
| WeilConjectures.CategoryTheory.SecondFiltrationIncomingRowCover | unclaimed | Adopted source API; untouched. |
| WeilConjectures.CategoryTheory.SecondFiltrationRowBoundarySubobject | unclaimed | Adopted source API; untouched. |
| WeilConjectures.CategoryTheory.SecondFiltrationRowCohomology | unclaimed | Adopted source API; untouched. |
| WeilConjectures.CategoryTheory.SecondFiltrationRowCycleComparison | unclaimed | Adopted source API; untouched. |
| WeilConjectures.CategoryTheory.SecondFiltrationRowGradedCycles | unclaimed | Adopted source API; untouched. |
| WeilConjectures.CategoryTheory.SecondFiltrationSignedFirstPage | unclaimed | Adopted source API; untouched. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Same comparison and step values through existing imports; no declaration edit. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Same comparison and step values through existing imports; no declaration edit. |

Repair of the return at a81b6d35e: the Users table now explicitly includes
Sheaf.AlgebraicGeometry.QcoherentComparisonDegreeZero, which uses the Ext-universe
and module-comparison API. Current main's new comparison component/naturality
lemmas and the degree-zero consumer are preserved. The now-restored normalized
pullback-square consumer receives only the total-complex import migration. Current
main's RingedSiteCechRefinementSquare no longer imports the retired module and its
new proof is preserved by omitting the stale sandbox adaptation.

## Status

landed 20261021T061643-L-1806495 2026-10-21 (merge of deliver/S2/Sheaf.CategoryTheory.DoubleComplexTotal)
