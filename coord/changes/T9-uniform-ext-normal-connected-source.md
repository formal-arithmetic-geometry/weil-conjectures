# AlgebraicGeometry.ProEtale.uniformConstructibleExt_normalConnectedSource

## Reason

Prove the original explicit cutoff in the supported case of a nonempty connected source
with normal stalks. The existing conditional theorem fixes the finite model before the
target; the declared normal-lattice theorem now discharges its antecedent for that very
model. This is a partial proof of the assigned item. Its disputed unconditional statement
and every existing signature remain byte-for-byte unchanged.

## Old

The declaration did not exist. No existing signature, definition, attribute, instance or
public import is changed.

## New

The new theorem is proved from existing declarations; no new hole is introduced.
A private proof import of Sheaf.Paper.NormalLisseFiniteCoefficientLattice supplies the
normal-source lattice. The private `import all` of
Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality exposes its proved free_of_comap
and free_of_iso helpers for coefficient transport. Neither module is publicly re-exported;
the latter's geometric local-triviality theorem is not used.

```lean
theorem uniformConstructibleExt_normalConnectedSource
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k]
    (hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (S Z U : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j]
    [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j]
    [Nonempty S] [ConnectedSpace S]
    (hnormal : ∀ z : S, IsDomain (S.presheaf.stalk z) ∧
      IsIntegrallyClosed (S.presheaf.stalk z))
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) S))
    (hL : IsLisseCoefficientModule (coefficientHeartRingObj Λ) L) :
    ∃ d : ℕ,
      (d : WithTop ℕ) = relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j +
        cohomologicalDimension ℓ (Fact.out : ℓ.Prime) S + 2 ∧
      ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
        ∀ q : ℕ, d < q →
          Subsingleton (Abelian.Ext
            ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) i).obj
              ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj Λ) v).obj L))
            N.obj q)
```

The unclaimed direct consumer `Sheaf.Paper.ConstructibleCompactness` is also adapted.
Its private helper `uniform_ext_standard` needs only the already proved existence clause.
It now calls `uniformConstructibleExt_exists` directly, avoiding the disputed theorem.
Its signature, every other proof, all attributes and imports are unchanged. This is a
proof improvement in an unclaimed module, not a forced adaptation of another group's item.

Old proof invocation:

```lean
  obtain ⟨d, hd⟩ := (uniformConstructibleExt D ℓ hℓ Λ hΛ D.k
    (Or.inr ⟨RingEquiv.refl _⟩) X).1 ⟨C, hC⟩
```

New proof invocation:

```lean
  obtain ⟨d, hd⟩ := uniformConstructibleExt_exists D ℓ hℓ Λ hΛ D.k
    (Or.inr ⟨RingEquiv.refl _⟩) X ⟨C, hC⟩
```

## Users

The new name has no existing users. All existing declarations and public imports are
unchanged. The following is the complete transitive importer inventory from
`tools/downstream.py Sheaf.Paper.UniformConstructibleExt --names`; the two direct
importers are ConstructibleCompactness and FiniteWindowBounded.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.UniformConstructibleExt | T9 | Adds the proved normal-source special case. |
| Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingProjectionSquare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorCoherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorTransposeAssembly | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.DeligneLaumon.GeometricConstituentOrbit | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.DeligneLaumon.PairEigenvalueGeometricConstituent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.DeligneLaumon.SemisimpleFrobeniusOrbitDescent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicCompletedProjectionShift | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicNormalizedPurityLift | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicProjectionShiftData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicTraceTensorShift | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicTraceTransposeData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicUnitTraceConstruction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicUnitTraceReductionData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicUnitTraceScalarData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AdmissibleVerdierExchange | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AffineCounitScalar | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AffineLineAdjunctionAssembly | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AffineSpaceProductDomain | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AffineSpaceRationalInduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AffineSpaceTraceProductData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ArithmeticRoots | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.BrownExceptionalAdjoint | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.BrownHypothesesGeneration | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ChartCounitScalarTransport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ChartGeometricCounitEvaluation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CoefficientUnitTowerNormalized | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CompactSupportProjectionFormula | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CompactSupportTowerReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CompositionComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedHomChainRealization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedOpenCounitRealization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedOpenCounitUnits | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CondensedOpenUnitComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed at inspection | Its private helper now calls the proved existence clause directly; signatures unchanged. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.EtaleCtfChartDomain | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.EtaleSumCounitScalar | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ExceptionalReconstructionContext | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExceptionalFiniteCompatibility | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExceptionalNormalizedAdjoints | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExceptionalSystemAdjoints | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExceptionalSystemComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExceptionalSystemComponents | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExceptionalSystemDomains | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExceptionalSystemEvaluation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExceptionalSystemFiniteComposite | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExceptionalSystemIso | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExceptionalSystemLaws | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionCompletedStrictLimit | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionComposition | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionIntegralDescent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionIntegralModels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionLimitEquations | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionRationalComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionRationalDescent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionRationalModels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionReductionDescent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionReductionLimits | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionSourceNormalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionStrictLimits | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldExtensionTowers | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldOrientationSystemComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldOrientationSystemComparisonData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldOrientationSystemCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldOrientationSystemHeart | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldOrientationSystemNormalizations | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldOrientationSystemRigidity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldProjectionOpenSquare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldProjectionOriginWitnesses | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldProjectionProperSquare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldProjectionSystemData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldProjectionSystemSquare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldProjectionTensorConstruction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldPuritySystemTranspose | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldPurityTransposeArrows | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSupportEvaluation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSystemCocycle | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSystemCoherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSystemComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSystemEvaluation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSystemMixed | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSystemMixedCompatibility | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSystemModels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSystemRealization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FieldShriekSystemTransitions | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteCompactSupportDomains | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteOrientationReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteProjectionOperationPresentation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FinitePurityCounitSystem | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteReductionTensorFactors | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteReductionTensorPurity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteReductionThetaFactor | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteSupportCompositorCoefficient | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteSupportCompositorExistence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteWindow | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteWindowBounded | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.FiniteWindowUnbounded | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.GlobalIdentityNormalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.GlobalVerdierDuality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.GlobalVerdierDualityData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.HomChainPairingNaturality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralAdjunctionBijection | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralCoefficientModelComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralDirectImageTower | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralPurityCounitReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralStageProjectionReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.IteratedPurityScalarPasting | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.MateOpenCompactSupportExchange | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.MateOpenProperRestrictionIso | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.MateOpenRestriction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.MateOpenRestrictionMaps | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ModelCompactComparisonUnit | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.NonrationalCompositionSeed | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.OpenProEtaleCounitScalar | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.OrderedLineLevelBounds | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.OrderedTateScalarNormalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.OrderedTowerOrientation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.OrientationScalarTowerTransport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.P1CounitScalar | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.P1SplittingScalar | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PodCtfAdjunctions | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PodCtfPairingMaps | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PodHomChainCounitFormula | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PodHomChainCtfDomains | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ProjectionFiniteReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ProjectionFormulaCoherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ProperExceptionalRestriction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PulledOrderedLineSingle | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PurityFiniteReductionTransport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PurityPullbackLevelBounds | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PurityPullbackReductionTransport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PurityTensorMapNaturality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.PurityTowerReductionComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalAffineTensorCalculus | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalExceptionalRestriction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalP1Triangle | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalPurityComparisonDescent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalPurityScalarLocalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalPuritySourceLocalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalRestrictionGlue | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalScalarComparisonData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RawChartScalarCounitPasting | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RelativeKunneth | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RestrictionLocal | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothOrientationStageExchange | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityCompositionFactors | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityFieldExtension | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerBound | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerBoundsDomain | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerBoundsOperations | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerChartData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerCompactBounds | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerGamma | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerGammaData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerGluing | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerGluingData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerOpenHomComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerP1Data | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TensorHomExchange | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TensorMapPresentationIndependent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TensorMateInvertibleInput | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TensorTransposeTowerNaturality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerAdjointCompositorRealization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerGeometricPurityMate | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerNormalizationPreservation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerOrientationEvaluation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1ComparisonsWithLine | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1CtfData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1DiagonalProjectionFactor | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1DiagonalTransport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1FiniteAdjunctionAssembly | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1FirstTraceReordering | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1FixedTotalTensor | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1KernelFiniteComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1KernelScalarData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1KernelSplittingBaseChange | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1LevelCtfModel | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1LevelWords | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1ProjectionTraceIdentification | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1ProperCtf | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1PushCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1SecondTraceReordering | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1SingleLevelConstruction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1SingleLevelData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1SingleLevelTransport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1SingleLevelTriangles | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1TensorCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1TriangleFactorization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1TriangleWords | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1UniformCtfDomains | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerP1UniformPresentation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerPurityAdjointTransport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerPurityRealizedData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerTensorAdjointDomains | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerTensorTransposeWords | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerTracePurityComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerTracePurityComparisonData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerTraceScalarCounit | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TowerUniformEtaleDomains | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackCofinalModels | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackLineMembership | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackReductionData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackReductionTower | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackTateReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackTowerBounds | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.UniformTowerTensorClosure | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.VaryingRingGraphSummand | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.VerdierCoefficientRealization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.VerdierExchange | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.VerdierHomChainComposition | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.VerdierHomChainCompositionData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.VerdierIdentityProjection | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.WeilChosenDualityExchange | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.DncCoefficientTransportData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.Reduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptionalChart | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptionalConservativity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptionalObjects | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptionalRealization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.ReductionOrientation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.SectionScalarBaseChange | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralCompatibleComposition | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralKernelContractions | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralKernelTateComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralKernelUnitCounit | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.ScalarDenseRefinementSquare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Targets.AffineSpaceRationalLine | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Targets.PoincareUncurry | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.Targets.SmoothPurityQbar | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| TargetsCheck | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.PoincareDuality.Poincare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.PoincareDuality.Verdier | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.SmoothPurity.Defs | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.Statement | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.Additivity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.Basic | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.BorelMoore | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.CompactCohomology | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.CompactPullback | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.Correspondence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.CorrespondencePair | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.CurvePieces | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.Dualizing | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.FibreCoherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.FibreModel | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.FixedPoint | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.FixedPointScheme | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.Frobenius | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.GenericQuotient | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.HomologyUnit | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.KunnethVerdier | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.LocalTerm | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.LocalTermLocality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.Main | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.ModelExtension | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.OpenSquare | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.PointNormalization | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.Product | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.ProperCompatibility | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.ProperCurve | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.ProperPushforward | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.PullbackFamily | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.Stalk | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.Statement | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.SupportedPairing | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.TraceClass | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.WeilBaseChange | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.TraceFormula.WeilTrace | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.WeilSheaf.Curve | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.WeilSheaf.EulerProduct | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.Examples | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.LissePurity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.Weights | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unchanged consumer; not adapted | Existing statements and public import closure unchanged. |

## Status

landed 20261026T202237-L-3445340 2026-10-26 (merge of deliver/T9/Sheaf.Paper.UniformConstructibleExt)
