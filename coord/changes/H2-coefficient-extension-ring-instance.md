# Padic.coefficientExtensionRing

## Reason

The retained proof of `sf_directImage_torAmplitude` exceeded the 60-second file limit
against the original reducible coefficient ring. An isolated compile of the exact proof
against the unchanged published coefficient module reproduced this timeout in this session.
Profiling in the retained work localized the kernel cost to specializing the generic
module-sheaf tensor/cohomology proof to the concrete quotient ring. Reducible unfolding
selected large quotient-ring hierarchy terms at multiple levels. Giving the quotient a
named CommRing instance keeps those projections shared, and making the type an ordinary
definition avoids eager unfolding. The proof compiles with this repair.

`Sheaf.NumberTheory.Padics.CoefficientExtension` is unclaimed. The change is authorized
by the stage-3 definition-repair rule; no other group's module is edited.

## Old

```lean
@[reducible]
noncomputable def coefficientExtensionRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Type u :=
  coefficientExtensionIntegers l E ⧸ coefficientExtensionIdeal l E n
```

## New

```lean
noncomputable def coefficientExtensionRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Type u :=
  coefficientExtensionIntegers l E ⧸ coefficientExtensionIdeal l E n

/-- The coefficient ring carries the quotient commutative-ring structure. Naming this
instance keeps specialization from selecting distinct quotient instances at each level
of the ring hierarchy. (blueprint: def-weil-l-adic-coefficient-extension). -/
noncomputable instance coefficientExtensionRingCommRing (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    CommRing (coefficientExtensionRing l E n) :=
  inferInstanceAs (CommRing (coefficientExtensionIntegers l E ⧸ coefficientExtensionIdeal l E n))

/-- The quotient algebra over the integer ring, also supplying its scalar module structure.
(blueprint: def-weil-l-adic-coefficient-extension). -/
noncomputable instance coefficientExtensionRingAlgebra (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Algebra (coefficientExtensionIntegers l E) (coefficientExtensionRing l E n) :=
  inferInstanceAs
    (Algebra (coefficientExtensionIntegers l E)
      (coefficientExtensionIntegers l E ⧸ coefficientExtensionIdeal l E n))
```

## Users

The quotient type, ideal, all ring operations and all mathematical predicates are
unchanged. The new CommRing and Algebra instances are exactly `inferInstanceAs` of the previous
quotient instances, so their projections are definitionally equal to the old instances.
The first direct-consumer check found that the scalar module in `LisseAdicSheaves`
needed the quotient algebra to be registered explicitly; that API is now provided here
without changing the consumer. The
transition-map definition in the changed file is unchanged and compiles. No target
signature, coefficient construction or mathematical statement is altered.

The table lists every transitive importer from `tools/downstream.py` and its current
holder. Textual users were checked for use of the same quotient; other entries only
import it indirectly. All 24 original direct consumers and the residue-test module compiled individually
against the changed coefficient module. The initial LisseAdicSheaves scalar-module
failure was repaired by adding the canonical quotient Algebra API above; its original
source then compiled. The subsequent source refresh added the direct importer
`Sheaf.NumberTheory.Padics.IntegersCosetBasis` and the textual consumers
`Sheaf.Paper.IntrinsicComparisonConstructibility`,
`Sheaf.Paper.IntrinsicComparisonTorAmplitude`, and `Sheaf.Paper.TwistFrobeniusScalar`.
All four original sources compiled against this repair in the current session.
No consumer source adaptation is proposed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Algebra.Homology.RationalTermHomComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Algebra.Homology.RingedSiteTorFlatModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Algebra.Homology.ScalarInternalHomAdjunction | F3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Algebra.Homology.SemidualizingRHomConservative | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction | S5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Algebra.Homology.SitePerfectTorWindow | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization | F9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusUniversalHomeomorphism | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | V4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | G6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | G1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.AmplificationConsequences | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.BoundedConstructibleHomOfPreserves | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorHomAdjunctionOfPreserves | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | Y6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ClassicalModuleWeakSerre | G4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange | G9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ClopenSectionComponent | A6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | D3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization | P9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen | X3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ComparisonTorInterval | H5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | X6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | E3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical | Q6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison | X5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction | J3 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ContinuousEtaleCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.Curve.FiniteMapAffineLine | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.Curve.ProperCurveCompatibleH1NoFixed | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EquivariantMarkedNodalAlteration | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude | R6 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | A9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EtaleLocalDualInterval | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport | T7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | H7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ExcellentEtaleConstantProjection | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ExceptionalBaseChangeReducesToProper | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula | H1 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction | G2 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | C9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedSubschemeDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence | H8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FiniteProetaleSmoothBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | G3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FormalPlaneAdjunctionLattice | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FrobeniusDetailed | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FrobeniusOpenSquare | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FundamentalGroup.CompactCharacterLogarithm | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FundamentalGroup.PadicCharactersH1 | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.FundamentalGroup.WeilTwistedPaths | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | T9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.GeometricSpecializationCategory | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | Q1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.IntegralLatticeCoefficientTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | H9 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | S6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence | S7 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.KummerCoefficientBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.LfpTensorSingle | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LisseLatticeClassSheaf | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LisseLatticeCoefficients | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LisseLatticePresentationTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LisseLatticeSliceTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LocalDimensionFunctionCalculus | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LocalSystemTensorMonodromy | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence | J5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.LocallyFreeTensorSingle | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.MultipointedCurveModification | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.NoetherianAffineLineUnit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility | H4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.OpenComparisonTensorNormalization | J6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.OpenDirectImageClassicalAmplitude | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.OpenProjectionSiteTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions | H4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | S8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.PrimePowerHomTensorTest | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage | D8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructibleLowerStar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | E6 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleComparisonTorsor | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleConstantModuleModelRigidity | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleConstantModuleRestriction | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ProEtaleContinuousCohomologyLimit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist | U6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsType | F6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian | J9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit | D9 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ProEtaleLeftComplete | U9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleLeftCompleteTruncationTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleLocalizationFilteredSection | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic | V5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence | V6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts | V7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ProEtaleOpenTensor | G5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtalePairFlasque | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleProductsDerived | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit | W6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal | U7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleTorsionStalk | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleTorsorComparisonAffine | K2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOriginEquation | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | B5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | M1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ProperGenericCurvePreparation | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | X7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.PunctualStrictCompletionTest | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.AlgebraicGeometry.PurSupportExact | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.PurityAffineLineComponents | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.RegularImmersionLinearization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.RegularSpecializationGeometry | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.RelativeFrobeniusFinite | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.RelativeFrobeniusGeometricFiber | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.RelativeFrobeniusIntegralUniversalHomeomorphism | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest | X9 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.RingDerivedScalarExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso | M2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SemistableMultipointedPair | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SfClassFullCohomologicalDimension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.SfEtaleExchanges | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.SfFullCdWeaklyContractibleTest | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.SfFullcdUsedClass | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange | Y6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.StableModificationStabilityLocus | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.StrictLocalEtaleDimensionBounds | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | Y7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SupportLocalizationTriangle | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.AlgebraicGeometry.SupportQuotientFlat | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SupportQuotientProduct | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SupportTriangleCompatibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SupportTriangleConstruction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.SurjectiveClosedModuleInvariance | K7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.TorsionLocalSystemMonodromy | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.TorsorComparisonGlue | K6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | K8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | K7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingOperations | U8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | U9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | K9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | J4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.CoefficientFiniteLocalSystemsPullback | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.DerivedCategory.FiniteTorAmplitudePerfect | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect | H4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.ScalarLocalizationDerivedHom | K4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope | M6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.SiteTorIntervalRestriction | M7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.Sites.CoherentConservativeReflection | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.Sites.CoherentObjectApproximation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.Sites.CoherentToposRepair | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.SystemLevelLeftExtension | M8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.ConstructibleSheaf.GaloisDescentMonodromyTensor | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.DeligneLaumon.AffineGeometricComponentsFiniteExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.DeligneLaumon.SmoothAffineFrontierStratification | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.LinearAlgebra.ContinuousIntegralMatrixLocalSmith | C4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.LinearAlgebra.ContinuousIntegralPivotSplitting | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.NumberTheory.FrobeniusRootsOfUnityPower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.NumberTheory.Padics.AdicLimitFiniteModules | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.NumberTheory.Padics.CoefficientExtension | unclaimed | remove reducible attribute; expose canonical quotient CommRing and Algebra instances |
| Sheaf.NumberTheory.Padics.CoefficientExtensionFinite | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.NumberTheory.Padics.CoefficientExtensionSmallLog | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.NumberTheory.Padics.ContinuousUniformizerDivision | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.NumberTheory.Padics.DeepPrincipalUnitLog | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.NumberTheory.Padics.IntegersCosetBasis | unclaimed | Direct importer; uses the unchanged integer ring and ideal only, not coefficientExtensionRing; no source adaptation. |
| Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.NumberTheory.Padics.IntegersProfiniteTower | D2 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.NumberTheory.Padics.LatticeStabilizerOpen | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.NumberTheory.Padics.PadicIntegersIntegralClosure | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | V5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicClosedConstructible | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicCoefficientDatumCompleted | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicCompletionReduction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicConstructibleFiniteReductions | Y8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.AdicGlobalDerivedHom | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicPullbackPresentationTransport | M9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.AdicPurityObjects | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.AdicReductionAdjunction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicResidueLissePerfectLift | V6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.AdicStratifiedPerfect | P5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdicTorFlatCohomology | S6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AdmissibleLattices | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AffineLineInvariance | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AffineLineSupportGeometry | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AlgebraicNumberRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AlgebraicallyClosedCoefficients | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AmbientCompleteRawSystem | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.AmplificationProper | P6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ArithmeticRoots | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.BoundaryExceptionalComparisonData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BoundaryQMaps | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BoundaryQTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BoundedBelowCtfReflection | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BoundedConstructibleComplete | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | H5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BoundedConstructibleTower | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BoundedSiteAdjunctionTranspose | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange | F7 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CanonicalOriginCompactSupportComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CanonicalWeilFundamentalRepresentation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CartesianCoefficientTwists | Q4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CartesianCoefficients | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | E2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CartierClassAgreement | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ChernFlagFormula | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ChosenFixedCompactSupportExchange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ClosedSupportConstructible | N4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefDerivedSystemEvaluationCalculus | P1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientCohomologyModules | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint | P2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientExtensionReductionModel | X9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientFiniteDescentHom | E4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientFiniteDescentLisse | F1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientFiniteDescentObjects | U5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientFiniteDescentSections | T7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientFrobenius | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CoefficientHeart | X8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientHeartCommonStratification | F2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientHeartFiltration | P4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientHeartGeneration | P7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientHeartSmall | F3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientHeartTriangulated | Y5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientRingedSequenceSite | V4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientSystemDerivedComparison | Q2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CohomologicalSmoothnessComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CohomologicalSmoothnessFiniteComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CommonStageCalculus | G6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CommonStageLisse | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CommonStageLocallyFree | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactFiberStalk | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CompactSupportCoefficientChange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CompactSupportDirectImageTriangulated | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactSupportReductionTower | F8 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactSupportSiteCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactificationCoherence | F9 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactificationLocalizing | F4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ComparisonBoundZero | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ComparisonPullbackExact | K3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ComparisonTorAmplitude | G1 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompleteProetale | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompleteResidueCohomologyBounds | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedCoefficientPresentationTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | Q3 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedConstantFiniteComplexRealization | S7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedDerivedInverseLimit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedDirectImageLimits | Q7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedExchangeCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedExtensionZeroComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedIntegralCoefficientGerm | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedIntegralCoefficients | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CompletedIntegralConstantMapOfUniverses | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedMapReduction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedOpenExchangeTransport | R1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedOperationTowerSubstitution | T1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedProjectionCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedPullbackAdjunction | M2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedPullbackReduction | D9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedPullbackTensorComparison | Z6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedPullbackTriangles | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedPullbackUnitTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedRlimFunctor | M3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedScalarShift | G2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedTowerCompatibility | P8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedTowerDerivedLimitFunctor | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.CompletedTowerDirectImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletedTowerPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletionMap | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletionMateComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompletionSupportedConstantComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CompositeIntegrationCounit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConcentratedComplexShift | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedAmbientExchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedERealization | Y9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedOpenExtensionProducts | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.CondensedPointCoefficients | G3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.CondensedPointSupertrace | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedTateRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CondensedZlReduction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ConstantCoefficientObjectsConstructible | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | Z5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstantModelTorAmplitude | G4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstantRealizationDerivedScalarExtension | Z9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstantTowerDirectImageNormalization | U6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstantTwoTermResolution | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstantWeilStructure | Z6 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ConstantWeilStructureStageIndependence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleCompactness | U7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleCompleteBaseChange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | Z7 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ConstructibleExceptionalInverseImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleExtContinuity | U8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ConstructibleHeart | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | P8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleInternalHomContinuity | R2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleIntervals | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ConstructibleIntervalsUnordered | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleSingleDegreeComparison | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.ConstructibleStandardTStructure | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ConstructibleTruncations | Z8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousConstructibleModule | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CurveMiddleExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedComplete | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedCompleteIntegralDetailed | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedCompleteOnSlices | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedCompleteUnrestricted | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | T2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedInternalHomFilteredColimit | R3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedNakayama | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedNakayamaFirstReduction | T3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedNakayamaResolution | U1 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.DerivedPullbackTensorHom | E9 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.DerivedPullbackTensorIso | C6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DetIndHeartIISums | C5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DiagonalTowerLimit | G3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DiagonalTowerSystem | H4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DirectImageChangeRingTranspose | J2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DirectImageCtfOpenTor | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DirectImageTorAmplitude | H2 | proof completed using the canonical quotient ring hierarchy; signature unchanged |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.DirectedGaloisFiniteTensorGenerators | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ECoefficientSmoothBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EmbeddingExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | S1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | F8 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | N1 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.EtaleGeometricBiduality | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.EtaleIsoDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleLocalMonodromyRealization | U9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.EtaleMonodromyRealizationData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleOriginDerivedCategory | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EtaleWeilSheafEquivalence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.EvenTensorPositivity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ExactFunctorDerivedLimit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | C3 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ExceptionalCoefficientComparison | S4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ExceptionalMateSiteComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ExchangeProjection | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | P9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ExternalRHomConePairing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FdCoefficientComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FdPullbackComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FibreFunctorBasepointTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FilteredCoefficientTensorBounds | Q5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | G7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteCoefficientDirectImage | G8 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCoefficientFlatModel | K1 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCoefficientPoint | A3 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteCoefficientTensorCtf | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCompactSupportConstructibility | G9 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteComparisonLocalizing | V7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteConstantH1Pi1 | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteConstantModelResolution | V6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteCtfTriangulated | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | V8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteExceptionalInverseImage | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteExtensionProperBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteExtensionReductionConeBound | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteFieldExceptionalPreservation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteFieldFiber | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | U3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteFieldSheafScalarExtension | V7 | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | N2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteFreeHomComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteLevelProEtaleBaseChange | H5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteLevelRectangle | Q6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteLevelRingedProEtaleBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteMittagLeffler | A3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteProjectiveTensorProducts | W6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteProperBaseChange | U4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteProperLocalizing | V9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FinitePullbackTensorComparison | S1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteReductionConstructibility | V2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteReductionReconstructionCompleted | S8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.FiniteResidueDualizing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteRingCompactSupportProjectionMap | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteRingSectionDeformation | V3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteSmoothCanonicalInterfaces | K3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteStageDirectImageTorAmplitude | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteStagePairCategory | E5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteSystemPullbackCoherence | Q8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteTateSiteDescent | V9 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteTorAmplitude | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteTorAmplitudeProEtaleModule | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteTorAmplitudeSites | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteTorInternalHomAnyField | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteTorStability | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteTorsionConstructibility | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FiniteTypeExceptionalInverseImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteWindow | W5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteWindowBounded | C1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FormalClosedSupport | Q9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FormalClosedSupportDerived | W5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FormalClosedSupportII | M2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FormalClosedSupportIILimits | W6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FourArrows | R5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FourCorners | W4 | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.FourierAdicArtinSchreier | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FourierSetting | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FourierTraceFormula | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | R3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | same quotient and operations; canonical instances definitionally equal |
| Sheaf.Paper.FrobeniusGeometricExchange | A2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.FrobeniusSquareExchange | J3 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.FullCDClassRestriction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.GaloisAdicFromFinite | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GaloisFiniteModuleLift | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GaloisFiniteTensorScalar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GaloisLisseCorrespondenceData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | C2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.GeneralNearbySliceTest | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GeoCartierExponentIndependence | Y9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GeometricHypotheses | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GeometricStalkPerfect | W7 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IndConstructibleExtensions | K4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IndConstructibleFilteredColimits | M1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IndHeartCanonicalPresentation | W8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IndHeartFullFaithfulness | M2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IndHeartIIVanishing | E9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralCanonicalTruncations | E7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.IntegralCoherenceTower | B2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | V4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | W7 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | W3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralComparisonRealizationModels | R6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralComparisonSequenceSystems | R7 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralConstantModelHeart | C2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstantModelHeartClosure | H7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness | X2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstructibleCompactness | E7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstructibleExt | J9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstructibleHeart | P1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstructibleLinear | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralConstructibleTriangulated | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralCriterionReductions | X3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralCtfTriangulated | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralDerivedCoefficientData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralDerivedOperations | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralDerivedOperationsOnSlices | Y2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralDerivedReduction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralExtensionByZero | A3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralFinitePullbackComposition | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralHeartDualizable | C5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralHeartLocalModel | C3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralHomReduction | M4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralHomReductionComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralLfpConstantModelComparison | H6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralLineTensorComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | S3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralModels | D4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralModelsOperations | N1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | H7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralOperationsScalarComparisons | Y3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralOperationsScalarExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralOperationsWellDefined | G1 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralProperBaseChange | B4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralProperDirectSums | F5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralPullbackComparisonRealization | A5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralPullbackComposition | A7 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralReductionTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralReductionTowerCanonical | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralReductionTowerUnrestricted | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralReductionTowerWellDefined | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted | P3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralResidueTor | N2 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralScalarExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralScalarExtensionConstructible | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic | N3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralScalarExtensionUniverses | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralScalarExtensionWellDefined | P4 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | Z6 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntegralStratumExtBound | K1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralStratumHomFormula | Y9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralTStructure | G6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralTensorProduct | N3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralTensorPullback | J2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralTensorShriek | F2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralTowerLimitComparison | J1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralTwistBaseChange | J4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralTwistScalarCoherence | N4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntegralUniformCoefficient | K5 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.InterchangeProperPasting | S4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.InternalHomPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | C3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntrinsicComparisonConstructibility | unclaimed | Same quotient type and operations; canonical instances definitionally equal; no source adaptation. |
| Sheaf.Paper.IntrinsicComparisonTorAmplitude | unclaimed | Same quotient type and operations; canonical instances definitionally equal; no source adaptation. |
| Sheaf.Paper.IntrinsicCompletion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntrinsicCompletionCompleted | M5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IntrinsicFiniteTorsionConstructibility | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IntrinsicQbarCategory | Z8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.InverseImagePullbackComparisonDerived | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IsomorphismDerivedPullback | C4 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IsomorphismReductionTower | N4 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.IteratedWeilMap | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.KoszulCompletionScalarComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.KoszulQuotientConeIsIso | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.KoszulQuotientLimit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.KoszulQuotientTensorAugmentation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.KummerAdditivity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticeClassDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticeClassPresheaf | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticeCosetLocalSurjectivity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticeCosetMap | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticeGluedRationalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticeGluedRationalizationIso | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticeMatrixNeighborhoods | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticePairDescentData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticePairEffectiveDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticePairLocalMatrix | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticePairMatrixAtBasis | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticePairRestriction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticeSectionMatrix | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticeSheafBasic | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LatticeSheafLocallyConstant | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LevelwiseAdicTruncations | S9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseAdicAutomorphismPullback | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.LisseAdicFiberFunctors | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseAdicSheaves | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.LisseCoefficientFiberComparisons | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseCoefficientFiberEndomorphisms | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseCompletedSystemComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | H8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseFiniteCoefficientModel | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.LisseFiniteHomLift | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseIntegralScalarFiberIsomorphism | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseIntegralSmallCoefficients | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseRankOneAut | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseRationalScalarFiberMaps | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LisseScalarFiberMaps | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.LisseScalarFiberReductions | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LocalFreeTensorUnit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LocalizedTStructure | D2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LocalizedTopChern | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.MateOpenRestriction | D7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.MixedReductionUnit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.MixedWeightsStability | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ModificationsZariskiRefinement | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | M3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NearbyClosedImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NearbySpecializationSlice | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NearbySpreadOut | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NilpotentKoszulCompletionUnit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NilpotentKoszulGradedTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | P2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | M7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NormalizedDVREffectivity | J6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NormalizedDVRTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.NormalizedEtaleOriginWitnesses | A8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.OpenComplementUnconditional | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | T2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OpenExtensionFiniteTor | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | X5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrgogozoInductionData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedClosedBaseRestriction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedConstructibleSetSheaf | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedConstructibleSheaf | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedConstructibleSheafVanishing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedHypercoverDescentDatum | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedMaximalPointFiniteness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedNearbyCycles | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedProductPointsConservative | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedProperFibreExchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedProperImageConstructibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.OrientedSourceLocalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PadicIntegersInvertEll | J7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcActualRingedExchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcActualScalarPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcActualStrictPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcAutomorphismTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcCommonStageCones | M9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcCompletedPullbackActual | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcConeIndependence | P5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcDerivedProductRepresentation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcDescentFunctors | C2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | P6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcFilteredRetractDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcFiniteCompletedCoefficientMap | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcFiniteRawScalarComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcFiniteStageKaroubian | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcIdempotentCompleteTriangulation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcQbarCategory | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcQbarCompletedPullback | P7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcQbarIdempotentComplete | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcRationalCategory | P8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcRationalTransport | P1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcRectangleDerivedLimit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcRoosTriangle | Q4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcScalarExtension | P9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcSupportCondition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcUniformCompleteTriangulated | Q5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcVerdierAxioms | R3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PbcWeilCategory | S3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PerfectProjectionFormula | A4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PointDerivedHomEvaluation | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PointFibreDerivedTensorBasic | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointFibreEquivalence | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PointReductionUnitNormalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PointReductionUnits | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointSectionsDerivedReduction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointSectionsFiniteReduction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointSectionsFiniteness | P3 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PointSectionsScalarExtension | P4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PointSectionsTensorShift | Q1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PotentialRegularBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PreservationConstructible | B5 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PrimeFieldTensorDevissage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ProEtaleConstantModulePullbackComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleConstantModulePullbackHomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleConstantReductionTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.ProEtaleConstructibleExactClosure | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleConstructibleOrigin | B2 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback | W4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses | R1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleResidueTorTest | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | B6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProjectionFormulaBaseChangeNaturality | R4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ProjectionFormulaIdentityCompactification | S1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProjectionSectionNormalization | X7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperBaseChangeFourArrows | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperBaseChangeFourCorners | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperBaseChangeRational | E9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperHeartBound | K5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperHeartBoundLattice | G2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperHeartBoundReduction | Y5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperHeartBoundTorsion | J4 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperOpenCoefficientMate | X5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperOpenCoefficientRefinement | S5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperOpenTowerComparison | Q4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PullbackCoefficientIterateCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PullbackTorAmplitude | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.Pur9Invertible | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurAdicScalarExtensionTorBound | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PurEtaleLisseStratumCompact | D5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurEtaleScalarMateProjection | B7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | Y2 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PurInverseImageTensorHom | R1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurLisseMorphismRigidity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurReductionLimitShiftAdjunction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurTwistSheafLocallyFree | K7 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PurityAffineChartBounds | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PurityAffineLineDatum | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityChernClasses | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityComparisonUnitInjectiveModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityConventions | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityCoprojection | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | R2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityDivisorClass | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityDncComparisons | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityDncFamily | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityDncFiniteRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityDncInvariance | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PurityFiniteSetting | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.PurityFrameClass | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityFrameKummer | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityGysinStructure | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityLisseUniqueness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityNormalBundle | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityNormalCone | X9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityRegularSection | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PuritySectionInvariant | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PuritySectionInvariantCompared | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PuritySourceTransports | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.PurityVectorBundleZeroSection | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarCompactSupportBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarIdempotentComplete | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.QbarOrdinaryAdjunction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarProperBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QbarTwistCommonStage | R1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QcqsCompactSupportRealization | D3 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalClosedSupportConstructible | C1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalOpenDirectImageConstructible | Z5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalRestrictionGlue | R9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.RationalStalkExact | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalizationIdempotentComplete | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RationalizationKaroubi | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RealBoundaryLocalConstants | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RealSheafSections | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ReconstructionUniformTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RefinementCoefficientMate | X6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RefinementComparisonIsomorphism | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.RefinementExchangeCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ResidueLissePerfectLift | Q6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ResidueLisseProjectiveModels | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.RestrictionDirectImage | Y5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RestrictionLocal | R3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RestrictionOfScalarsExact | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RingedCoefficientProjectionCocycle | C4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RingedPushforwardCompletion | T6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.RingedRefinementCoefficientSquare | D2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SbcCompletedOperations | C5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ScalarExtensionComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ScalarExtensionExact | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ScalarExtensionExactIntrinsic | D4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | D3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SectionDerivedRealization | T8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SectionDerivedTensorData | U6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SemilinearDerivedCalculus | T7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SemilinearDerivedSections | Q8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SemilinearGeometryCore | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SemilinearGeometryDerived | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SemilinearGeometryOps | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SemilinearSystemModels | U8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SequentialDerivedInverseLimit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SequentialDerivedInverseLimitCompleted | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SequentialDerivedInverseLimitFunctor | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfBidualityClass | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfCommonStageDirectImage | E1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfCommonStageWeilCohomology | V2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfCompactSupportRestrictionOfScalars | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfConstructibleHeart | E3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfDerivedComplete | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfDerivedDirectImage | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SfDirectImageCTFNonproper | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SfExchanges | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | K9 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SfIntegralConstructible | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfIntegralConstructibleLinear | V8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfIntegralConstructibleTriangulated | Q9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfIntegralDirectImageConstructible | M5 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SfIntegralReductionTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SfPreservationClass | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SfRationalBoundedConeTorsion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfRationalizationKaroubi | C8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfScalarExtensionComposition | C9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SfWeilSheafComplex | E4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SitePerfectComplex | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothExceptionalPreservation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothLisseIntegralLattice | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothProperDatum | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityCoefficientTowers | Y6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityCoefficientTowersAbelian | D5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityCompactProjectionBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityMap | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityNormalizedTowers | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint | Z5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityTowerInjectiveComponents | X8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityTowerLevels | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SmoothTrace | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SpDirectImageEtaleMate | V4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.StandingExceptionalBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.StandingExceptionalComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.StratifiedLattice | M6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.StratifiedOrientedCover | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.StratumScalarExtension | W2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | D6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.StrictTowerOperations | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedCohomologyHom | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedCup | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedHomAdjunctionTranspose | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedHomPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SystemNormalizedTensorClosure | U2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.SystemOperationExchangeRealization | K1 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.SystemTensorMateArrows | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TateInverseLimitBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.TateTwistLocallyFree | S7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TorsionLimitSheafCompleteness | B7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TowerPreservation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TraceBaseChangeFirst | E1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TraceExceptionalAdmissibility | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.TraceFixedScheme | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.TraceFormulaCoefficientSetup | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TwConventions | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Same quotient type and operations; canonical instances definitionally equal; no source adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | G5 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.UnboundedLocalizingPullback | Y7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.UniformCompleteTriangulated | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.UniformConstructibleExt | X9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.UniformConstructibleExtIntegral | K4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.UniformConstructibleExtRational | E3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.VectorBundlePurity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.VerdierExchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WContractibleCondensedScalarEvaluation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WContractibleConstantReductionsML | Z6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilCompactSupportCohomology | D8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilCompletedTensorReflector | R5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilComplexQbarIdempotentComplete | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilFourierInversion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilFourierTransform | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilIndSheafCategory | D9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilNumbers | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilOne | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilTensorProduct | F2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.WeilVerdierPreservationStrata | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Paper.ZlShriekComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.PoincareDuality.CompatibleIntegralRootBases | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.PoincareDuality.IntegralResidueLimit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.PoincareDuality.IntegralResidueQuotient | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.PoincareDuality.IntegralTateBasis | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.PoincareDuality.IntegralTateLocalLine | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.ProperBaseChange.SingletonSiteModuleComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.RepresentationTheory.ContinuousCoefficientSubquotients | Y9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.RepresentationTheory.LAdic | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.RepresentationTheory.ProfiniteStableLattice | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.RepresentationTheory.ProfiniteStableLatticeCore | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.RepresentationTheory.ProfiniteStableLatticeTopology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.RingTheory.AlgebraicRelativeDualizingIsomorphism | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.RingTheory.PseudoCoherentInverseRingReconstruction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.RingTheory.PseudoCoherentInverseRingReconstructionModels | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.RingTheory.RlimPerfectComplete | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecPurityRealSheaves.LogExpValuationConvergence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.CanonicalShriekExchange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SecSmoothPurity.DirectImageScalarExchange | E5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.FiniteCoefficientDirectImageExchange | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | U9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.OpenScalarExchange | S1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension | S8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | G1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | R3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | M1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.BoundaryAlphaNormalization | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.BrownHypothesesSmall | Z9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.ClosedCostalkDuality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.ComparisonOpenTensorCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.CompletedTensorShiftRight | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | same quotient and operations; canonical instances definitionally equal |
| Sheaf.SixFunctors.ConnectedEtalePerfectConstant | Z7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.EtaleGenericPerfectHom | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.EtaleStratifiedStalkIdentification | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.FieldTensor | N1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.FiniteCompactProetale | A2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.FiniteDualityClosedComparison | D6 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | same quotient and operations; canonical instances definitionally equal |
| Sheaf.SixFunctors.FlatModel | A3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.FlatModelGeneration | S3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.FrobeniusPointTransport | E7 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.FrobeniusSquareCartesian | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | Z8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntTensorProjection | G4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralExtHomContinuity | B8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralLisseReductionEquivalence | T1 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.IntegralTensorInverseImage | T4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.ModuleMapmodPullbackKFlat | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.OpenClosedFlatness | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | V7 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | F4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | A9 | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange | E8 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.ScalarSixPullback | U6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.SchemeGeometricFrobenius | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | H1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.SfCategories | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctors.UnboundedClassicalTruncation | Y2 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.SmoothPurity.UniqueAdjointCoefficients | F5 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Targets.PoincareUncurry | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Targets.VectorBundlePurity | F6 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.Topology.ProfinitePointSite | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.AlgebraicShriekCalculus | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.AlgebraicShriekRelativePerfect | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ClosedImageGenericAlteration | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ContractedComponentNoExtraGeneric | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.TraceFormula.CurveP1TreeLocalCriterion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.FinitarySiteCoherentGenerators | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.LocalMarkingLength | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.NodalContractionNormalizationBranches | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.OnePointDerivedRingIdentification | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.OrientedPointCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.OrientedPointNormalizedStratum | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | same quotient and operations; new named CommRing is definitionally the old quotient instance |
| Sheaf.TraceFormula.PolynomialDiagonalRhomReduction | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.TraceFormula.ProjectiveLineTree | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ProperBaseChangeCoherentConservative | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.SemistableMarkedPoint | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.StableCurveDiagramNoetherianModel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.StableModificationConstructibility | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.StableModificationSpreading | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.TwoTermPerfectDeterminant | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.UpperShriekBoundedCoherent | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Indirect importer; same public definitions and statements, no source adaptation. |
| Sheaf.TraceFormula.ValuationReducedFibreNormalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| TargetsCheck | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromyFrobenius | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalk | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.FourierTransform.Perverse | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | D3 | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.SmoothPurity.Defs | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.Statement | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.TraceFormula.Basic | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.TraceFormula.Statement | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.Curve | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.Defs | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.Localization | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.Operations | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.Examples | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |
| WeilConjectures.ZetaFunction.Weights | unclaimed | indirect importer; no occurrence of changed definition; statements and data unchanged |

## Status

landed 20261019T034300-L-417146 2026-10-19 (merge of deliver/H2/Sheaf.Paper.DirectImageTorAmplitude)
