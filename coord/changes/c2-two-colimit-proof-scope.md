# AlgebraicGeometry.ProEtale.constructibleCocone_isFilteredTwoColimit

## Reason

The five existing theorem proofs need private generic helpers, local inference instances,
and local elaboration controls. Server preflight conservatively classifies the added
universe, open, option and attribute commands as an interface-command change and requires
this record. No existing signature, attribute, public import, or definition body changes.
The added helper instances are local to the file or the object-descent proof, and
their declarations are private. No
persistent instance is exported. No target statement changes meaning.

## Old

The original proof context contains no added local attribute commands and no private
proof support sections. The five assigned theorem bodies are `by sorry`. The existing
public assembly theorem is preserved verbatim:

```lean
theorem constructibleCocone_isFilteredTwoColimit :
    (constructibleCocone X ℓ).IsFilteredTwoColimit where
  essSurjObj := constructibleCocone_essSurjObj X ℓ
  homSurj := constructibleCocone_homSurj X ℓ
  homInj := constructibleCocone_homInj X ℓ
```

## New

The assembly theorem above and every other existing signature remain verbatim.
The five assigned bodies are complete proofs. Proof-only imports remain private,
including `import all` for reusing existing proved private support lemmas. Added
private helpers contain no holes and are not used by existing public definition bodies.

The local instance priorities select existing sheaf limit/colimit instances and the
existing canonical category, closed and flat
resolution structures directly, rather than competing inference paths. The local
irreducibility attributes preserve sharing of large derived and scalar comparisons:

```lean
attribute [local instance 2000] CategoryTheory.Sheaf.instHasColimitsOfSize
  CategoryTheory.Sheaf.instHasColimitsOfShape CategoryTheory.Sheaf.instHasFiniteColimits
  CategoryTheory.Sheaf.hasLimitsOfSize CategoryTheory.Sheaf.instHasFiniteLimits

attribute [local instance 2000] CategoryTheory.Mod.monoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory

attribute [local instance 2000] CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Mod.hasFunctorialFlatResolution
  AlgebraicGeometry.ProEtale.sheafMonoidalClosed
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.upperStarFromPointComp
  AlgebraicGeometry.ProEtale.monoidal_upperStarFromPoint
  AlgebraicGeometry.ProEtale.monoidal_pointUpperStar
  AlgebraicGeometry.ProEtale.oplaxMonoidal_pointUpperStar

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

attribute [local instance] CategoryTheory.continuity_iso
  CategoryTheory.continuity_shift CategoryTheory.continuity_tri

attribute [local instance 2000] finiteBoundedTriangulated

attribute [local irreducible] finiteCoefficientDerivedHomEquiv
  finiteCoefficientDerivedAlgClHomEquiv finiteCoefficientDerivedRestriction
  finiteCoefficientDerivedFromAlgCl finiteCoefficientDerivedAdjunction
  finiteCoefficientDerivedAlgClAdjunction algClCommShift

attribute [local irreducible] derivedExtendScalarsCompIso
  finiteCoefficientDerivedTensorCompIso
```

Added `open ZeroObject`, `open Opposite`, and helper universes `v w vI v₁ v₂ u₁ u₂`
serve only private proofs. The existing namespace is closed and reopened for generic
helpers; the original public namespace and signatures remain identical. The default
`backward.isDefEq.respectTransparency false` is stated explicitly and locally overridden
to `true` for Hom surjectivity and the ambient comparison instances. Local linter options
only suppress unused section-variable warnings. No heartbeat or runtime limit is raised.

The five file-local inference helpers and two proof-local ambient helpers have the
following declaration prefixes. Their bodies construct or prove the stated structures; none is an assumption:

```lean
@[local instance]
private lemma continuity_iso : (homColimitProperty N c).IsClosedUnderIsomorphisms where

@[local instance]
private lemma continuity_shift : (homColimitProperty N c).IsStableUnderShift ℤ where

@[local instance]
private lemma continuity_tri : (homColimitProperty N c).IsTriangulated where

@[instance_reducible, local instance]
private noncomputable def algClCommShift (E : FiniteIntermediateField ℓ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).CommShift ℤ :=

@[local instance]
private lemma algClTriangulated (E : FiniteIntermediateField ℓ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated :=

@[instance_reducible]
private noncomputable def ambientCommShift (E : FiniteIntermediateField ℓ) :
    ((ambientCocone X ℓ).Φ E).CommShift ℤ :=

private lemma ambientTriangulated (E : FiniteIntermediateField ℓ) :
    letI := ambientCommShift X ℓ E
    ((ambientCocone X ℓ).Φ E).IsTriangulated := by

```

The private ambient cocone functors are written directly as the full constructible
inclusion followed by scalar extension. This is definitionally the same functor as
restricted scalar extension followed by the ambient inclusion; its comparison
isomorphism is the original whiskered constructible comparison with an explicit
associator. No existing public construction is edited.
The ambient Hom-surjectivity helper exposes the associator's identity components
and removes them by the category identity laws before transferring the given equality.

The ambient helpers are installed only in the object-descent proof, avoiding an
expensive global instance-index calculation for the large cocone expression:

```lean
let commShift : ∀ E, ((ambientCocone X ℓ).Φ E).CommShift ℤ := ambientCommShift X ℓ
have triangulated : ∀ E, ((ambientCocone X ℓ).Φ E).IsTriangulated :=
  ambientTriangulated X ℓ
```

## Users

Read-only `tools/downstream.py` with all five changed theorem names supplied via
`--uses` checked direct textual users and all transitive importers. The table includes
all its transitive importers and the item. Holders are taken from current module/node
claims. All public signatures and existing definition bodies are preserved; added
instances and attributes are local. No downstream adaptation is necessary or delivered.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.CoconeDerivedComparisonNormalForm` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CoefficientCoconeComparisonAgreement` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedCoefficientPresentationIdentification` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.AdicProperLocalizingAdjunctionComparison` | F6 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | X2 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.BrownHypothesesGeneration` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ChartCounitScalarTransport` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientFiniteDescentHom` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientFiniteDescentObjects` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientPushFilteredLegs` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | Q3 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationLocalizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementIdentity` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedBoundedHomContinuity` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedCompactSupportProjection` | D5 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeLeftAdjunct` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeRightAdjunct` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarPullbackCube` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedTateRealization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleAlgClTopologyComparison` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleCompactness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAdicProperBaseChangeRestriction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClOpenFiniteness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClOpenScalarComparison` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperFiniteness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperScalarComparison` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientCategory` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientDiagrams` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientEndpoints` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientExchange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFamilyPullback` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFiniteDiagonal` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFiniteRealization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientMaps` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientPullback` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientPullbackEndpoints` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientQuotientLine` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientQuotients` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientReference` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientScalars` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientSourcePullback` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerCoefficients` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTrace` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.EtaleAffineProjectionCoefficientMate` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.EtaleCtfChartDomain` | Q4 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | C4 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.EtaleSumCounitScalar` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | D3 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | M8 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientDescentTwoColimit` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCompactSupportDomains` | D4 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | J6 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProperLocalizing` | M6 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindow` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindowBounded` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindowUnbounded` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.GeometricCondensedFiniteScalarModel` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstantModelHeart` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleExt` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleHeart` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartDualizable` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartLocalModel` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartRealizationExact` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartResidueDual` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralModels` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTensorPullback` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.InterchangeProperPasting` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekCompositionModel` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | P1 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.NormAlgClInternalHomBaseChange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.OpenImmersionLocalizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.OpenProEtaleCounitScalar` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.OrderedCompactificationScalarSquare` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.P1CounitScalar` | U3 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.P1SplittingScalar` | V1 | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.PointRealizationCoefficientComparison` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBoundLattice` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBoundReduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperLocalizingAdmissibleCoefficients` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperLocalizingContinuousAlgCl` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperOpenBoundaryZero` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalClosedSupportConstructible` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalLocalizedHom` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalOpenDirectImageConstructible` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.SupportedCommonFieldScalarData` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.SupportedCommonFieldScalarModels` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.SupportedFiniteStageTopologyDefect` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.SupportedLatticeNormProjection` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TamePairProperGenerators` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TraceBaseChangeSecond` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExt` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtRational` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.VerdierCoefficientRealization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction` | W4 | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | E4 | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CommonFieldLatticeGenerators` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FieldTensor` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | M8 | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | Public interface unchanged; no adaptation. |
| `TargetsCheck` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | C2 | Five proof bodies completed; private proof context only. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Public interface unchanged; no adaptation. |

## Status

landed 20261023T040617-L-942185 2026-10-23 (merge of deliver/C2/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit)
