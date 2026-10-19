# AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient

## Reason

The predicate omits the finite-subextension-valued algebraic-closure coefficient used
by the assigned composition theorem and by EllAdic.lean. All continuous maps into
the topological algebraic closure and finite-subextension-valued sections are different
condensed rings. Add the missing latter case, retaining the former as a separate
compatibility case: existing continuous-coefficient interfaces remain meaningful.
This strengthens the generic theorems to include the paper's intended coefficient;
it neither identifies the two rings nor drops an existing case.
The predicate signature, all localizing-closure constructions and generators stay unchanged.

## Old

```lean
def IsLocalizingAdmissibleCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] : Prop :=
  (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ)))
```

## New

```lean
def IsLocalizingAdmissibleCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] : Prop :=
  (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))
```

## Users

The provider is unclaimed. The resumed downstream scan finds 372 transitive importers
and 27 other modules naming the predicate. Their signatures and coefficient constructions have been inspected. Retained compile logs
cover 20 provider/consumer modules; one further consumer check stopped because the published
build then lacked IntegralComplementFiniteness, so that check is not reported as passing. The preservation theorem's source and intended new
coefficient cases are the ones already recorded in its proof plan.

Sheaf.Paper.RationalExceptionalRestriction is unclaimed and is the only existing
consumer requiring a proof edit: line 134 gains Or.inl around hQ, selecting the
retained continuous-map branch. Every signature and every other line stays identical.
No theorem caller names rationalExceptional_preserves_constructibleFiniteTor.
Its earlier K8 independent-review instruction to retain the continuous coefficient
binder is respected. New modules use the added finite-subextension branch.

No Challenge declaration is edited. Targets use their fixed explicit coefficient
objects and their conclusions are unchanged; any review using this general predicate
should record the newly supported finite-subextension case separately from its
retained legacy continuous case.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | A4 (new in this delivery) | Selects the added finite-subextension-valued coefficient branch for open preservation; proved. |
| Sheaf.Paper.CompactificationRefinementIdentity | B3 (already landed; not adapted) | Generic admissibility hypothesis; existing proved dense identity law is reused unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.CategoryTheory.Triangulated.LocalizingFunctor | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ArithmeticRoots | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ChernFlagFormula | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.CoefficientHeart | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.CompactificationLocalizing | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ConstructibleCompactness | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.DetIndHeartIISums | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteComparisonLocalizing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteTorStability | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteWindow | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteWindowBounded | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FlagPullbackInjective | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FormalClosedSupport | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FlagLocalComparison | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.FormalClosedSupportII | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.FormalClosedSupportSheaves | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.FourierTraceFormula | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralModels | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralTensorProduct | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralTensorPullback | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.IntegralTensorShriek | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.InterchangeProperPasting | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.InternalHomDualTorAmplitude | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.LocalizedTopChern | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.LocallyConstantPerfectComplex | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.MateOpenRestriction | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.OpenPullbackGenerators | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProjectionSectionNormalization | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.Paper.ProperHeartBound | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.PurityChernClasses | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Forced proof adaptation: wrap hQ in Or.inl; signature and continuous coefficient unchanged. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.RationalPurityPresentation | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.RestrictionLocal | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.SfBidualityClass | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.UniformConstructibleExt | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.VectorBundleThomClass | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.VerdierExchange | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.WeilFourierInversion | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.WeilOne | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.ZlShriekComposition | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.SixFunctors.FieldTensor | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.FiniteCompactProetale | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.RationalOperations | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctors.RationalVerdier | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | not queried (not adapted) | Generic admissibility hypothesis includes the finite-subextension case; no proof adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Targets.PoincareUncurry | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Targets.SmoothPurityQbar | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| TargetsCheck | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.PoincareDuality.Poincare | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.PoincareDuality.Verdier | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.SmoothPurity.Defs | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.Statement | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.TraceFormula.Basic | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.TraceFormula.Statement | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.Curve | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.LFunction | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.Examples | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.Rationality | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.ZetaFunction.Weights | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | not queried (not adapted) | Generic admissibility hypothesis; selects only unchanged finite/integral branches; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | not queried (not adapted) | Transitive importer; no predicate occurrence or source adaptation. |

## Status

landed 20261019T154003-L-3023734 2026-10-19 (merge of deliver/A4/Sheaf.Paper.LocalizingLowerShriekComposition)
