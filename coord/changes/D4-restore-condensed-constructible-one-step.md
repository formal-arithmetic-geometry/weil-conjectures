# AlgebraicGeometry.ProEtale.condensed_constructible_one_step

## Reason

Restore the assigned quarantined module from its preserved source after the cluster
rollback recorded in coord/rework.tsv. The live path is absent, but the archived module
already contains a complete proof and nine proved private helpers. This delivery repairs
the missing library source. It does not close a proof hole or alter a mathematical statement.

## Old

The path lean/Sheaf/Paper/CondensedConstructibleOneStep.lean is absent. The preserved
source is quarantine/Sheaf/Paper/CondensedConstructibleOneStep.lean. Its declaration is:

```lean
theorem condensed_constructible_one_step
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T) M) :
    condensedConstructiblePiece T ℓ E ((DerivedCategory.singleFunctor _ 0).obj M) ∨
    ∃ (Z : Scheme.{u}) (i : Z ⟶ T),
      Exists fun [_hi : IsClosedImmersion i] ↦
      Exists fun [_hex : PreservesFiniteColimits
          (CondensedRing.lowerStar (Profinite.continuousMapRingObj E.val) i)] ↦
      ¬ Function.Surjective i ∧
      ∃ (MZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E.val) Z)),
        IsConstructibleModuleObject
          (condensedRingObj (Profinite.continuousMapRingObj E.val) Z) MZ ∧
        ∃ (A : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (Profinite.continuousMapRingObj E.val) T)))
          (f : A ⟶ (DerivedCategory.singleFunctor _ 0).obj M)
          (g : (DerivedCategory.singleFunctor _ 0).obj M ⟶
            (CondensedRing.lowerStar
              (Profinite.continuousMapRingObj E.val) i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ))
          (h : (CondensedRing.lowerStar
              (Profinite.continuousMapRingObj E.val) i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ) ⟶
            A⟦(1 : ℤ)⟧),
          Pretriangulated.Triangle.mk f g h ∈ distTriang _ ∧
          condensedConstructiblePiece T ℓ E A
```

## New

Restore the complete archive byte for byte at its original library path. The declaration
above, its proof, all nine private helpers, docstrings, visibility, universes, attributes,
and both public imports are unchanged. The restored file's SHA-256 is
`195237b77b0e48a76f536fed2a8f09b72640b7c59950e79ee09daeb92d9515c6`.

The proof uses the existing generic locally finitely presented open-piece theorem,
constructible pullback, the closed complement, and open/closed recollement. Mapping the
bounded-below recollement triangle into the ordinary derived category and transporting
its objects along the single-functor comparisons gives the required triangle. Identity
coefficient comparisons identify the open term as a locally closed piece. The empty-scheme
case is retained through the generic theorem's global finite-presentation alternative.

The unchanged node lem-weil-pbc-condensed-constructible-one-step, its Lean attachment,
and all six proof dependencies still describe this proof. No target definition changes
meaning and no target-statement review is reopened.

## Users

The live downstream query with --allow-missing has no source module to index. A separate
scan over both live library roots and both quarantine roots, with live files taking
precedence over archives, finds one direct consumer and 187 transitive consumers.
The direct consumer and DAG parent is Sheaf.Paper.CondensedConstructibleExtensionTower;
it applies the restored theorem at line 107. Its archived proof and dependency record
remain in place. There is no withdrawal, consumer adaptation, or change to any consumer's
mathematical statement. No held module is edited. The unchanged direct consumer compiled through lcompile.py in 8.8 seconds against the
restored item. The item compiled cleanly in 8.1 seconds against the published library,
and also in 20.0 seconds with a freshly compiled unchanged recollement dependency.
Those verification sources are not part of the delivery. The full affected-module
inventory is:

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | Not queried; not edited | Direct archived consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteTorStability | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteWindow | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.MateOpenRestriction | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperHeartBound | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.RestrictionLocal | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.SfBidualityClass | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Paper.VerdierExchange | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.FieldTensor | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.RationalOperations | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Targets.PoincareUncurry | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.SmoothPurity.Defs | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.TraceFormula.Basic | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.TraceFormula.Statement | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | Not queried; not edited | Transitive consumer; exact archived interface restored, no adaptation. |

## Status

landed 20261021T021911-L-2791017 2026-10-21 (merge of deliver/D4/Sheaf.Paper.CondensedConstructibleOneStep)
