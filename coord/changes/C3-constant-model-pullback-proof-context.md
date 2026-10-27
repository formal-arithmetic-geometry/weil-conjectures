# AlgebraicGeometry.ProEtale.pullback_constantModelConstructible proof context

## Reason

The original spelling of the specified-model isomorphism causes deterministic
kernel timeouts or the 60-second file timeout when specializing the generic
fiber-product comparison. This also happened after supplying scheme arguments
explicitly and expanding both square comparisons. Naming the repeated condition
makes the statement and proof share the same elaborated predicate. The canonical
stratum and cover objects, scalar modules and all hypotheses stay the same.
The original public theorem signature and canonical stratification definition are
verbatim. No source-library file changes. The new predicate has no choice or proof
data: it is precisely the existing Nonempty isomorphism proposition.

File-local elaboration options and local irreducibility attributes prevent expansion
of inverse-image and scalar-extension constructions during proof elaboration.
They are not exported. All original public imports remain verbatim.
This is a definition repair of ConstantModelPullbackStatement: its target-facing
meaning is unchanged, but its definition change is presented for independent review.

## Old

```lean
def ConstantModelPullbackStatement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : Prop :=
  ∀ {Y Y' : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y'] (g : Y' ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
    IsConstantModelConstructible Λ Y M →
      IsConstantModelConstructible Λ Y' ((CondensedRing.upperStar Λ g).obj M) ∧
      ∀ (S : Y.FiniteLocallyClosedStratification)
        (hS : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a))
        (U : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
        (P : ∀ (a : Fin S.n) (_ : (U a).I₀), Mod Ab.{u + 1} (scalarRingObj Λ)),
        (∀ (a : Fin S.n) (i : (U a).I₀),
          Mod.IsFinitelyPresented (scalarRingObj Λ) (P a i)) →
        (∀ (a : Fin S.n) (i : (U a).I₀),
          Nonempty ((CondensedRing.upperStar Λ ((U a).f i)).obj
              ((CondensedRing.upperStar Λ (S.immersion a)).obj M) ≅
            (finiteConstantScalarExtension Λ ((U a).X i)).obj (P a i))) →
        ∀ (a : Fin S.n) (i : (U a).I₀),
          Nonempty ((CondensedRing.upperStar Λ
              (((U a).pullback₂ (pullback.fst (S.immersion a) g)).f i)).obj
                ((CondensedRing.upperStar Λ
                  ((constantModelPullbackStratification S hS g).immersion a)).obj
                    ((CondensedRing.upperStar Λ g).obj M)) ≅
            (finiteConstantScalarExtension Λ
              (((U a).pullback₂ (pullback.fst (S.immersion a) g)).X i)).obj (P a i))
```

## New

```lean
def HasScalarModelOnRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {V X Y : Scheme.{u}}
    (v : V ⟶ X) (s : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (P : Mod Ab.{u + 1} (scalarRingObj Λ)) : Prop :=
  Nonempty ((CondensedRing.upperStar Λ v).obj ((CondensedRing.upperStar Λ s).obj M) ≅
    (finiteConstantScalarExtension Λ V).obj P)

/-- The two clauses of preservation: constructibility, and the same finite scalar models
on the base changes of any specified witnessing stratification and covers. The scalar
modules are quantified before pullback and occur unchanged on the right of each output
isomorphism. `pullback₂` retains the cover's index type and has members
`U_i ×_{Y_a} (Y_a ×_Y Y')`, with the second projection as covering map.
Source: blueprint pullback proof, "Constructible complexes", expanded local-model argument
(blueprint: lem-sfb-pullback-constant-model-constructible). -/
def ConstantModelPullbackStatement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : Prop :=
  ∀ {Y Y' : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y'] (g : Y' ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
    IsConstantModelConstructible Λ Y M →
      IsConstantModelConstructible Λ Y' ((CondensedRing.upperStar Λ g).obj M) ∧
      ∀ (S : Y.FiniteLocallyClosedStratification)
        (hS : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a))
        (U : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
        (P : ∀ (a : Fin S.n) (_ : (U a).I₀), Mod Ab.{u + 1} (scalarRingObj Λ)),
        (∀ (a : Fin S.n) (i : (U a).I₀),
          Mod.IsFinitelyPresented (scalarRingObj Λ) (P a i)) →
        (∀ (a : Fin S.n) (i : (U a).I₀),
          HasScalarModelOnRestriction Λ ((U a).f i) (S.immersion a) M (P a i)) →
        ∀ (a : Fin S.n) (i : (U a).I₀),
          HasScalarModelOnRestriction Λ
            (((U a).pullback₂ (pullback.fst (S.immersion a) g)).f i)
            ((constantModelPullbackStratification S hS g).immersion a)
            ((CondensedRing.upperStar Λ g).obj M) (P a i)
```

Unfolding HasScalarModelOnRestriction restores exactly the original two local-model
isomorphism clauses. No hypothesis, conclusion, cover index or scalar module is
changed. The original public theorem is proved by finite scalar presentations,
scalar-matrix inverse image and two fiber-product squares. The constructibility
clause reuses the existing private pullback_constructible with a proof-only import
all of Sheaf.Paper.UnboundedLocalizingPullback, whose module and DAG graphs do not
reach this item.

## Users

The downstream scan is conservative and includes transitive importers. Every
listed consumer sees the same proposition after unfolding; no adaptation is expected. Holdings are
irrelevant because no consumer file is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | C3 | Own predicate definition repair and completed proof. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.DeligneLaumon.QbarCurveDuality | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.AdicCommonStageHomTranspose | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.AdicNormalizedPurityLift | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.AdicUnitTraceConstruction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.AdicUnitTraceReductionData | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.AdicUnitTraceScalarData | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.ArithmeticRoots | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.CartesianSectionAdjointMates | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.CartesianSectionData | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.ChartDiagonalSourceMate | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.CommonStageFourierWeightUpper | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.CondensedExceptionalReconstruction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.CondensedHomChainRealization | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.CurveIntermediateExtension | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.CurveMiddleExtensionUpper | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.ExceptionalInverseImageExistence | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.ExceptionalRealizationNormalization | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.ExceptionalReconstructionComparison | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.ExceptionalReconstructionContext | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.FiniteTorStability | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.FixedStalkIdentificationReduction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.GeneralHomComparisonCocycles | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.GenericRetractSupportGluing | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.GeometricComparisonData | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.GeometricGeneratorProjectionDevissage | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.GeometricOperations | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.InverseContravariantBidual | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.NormAlgClInternalHomBaseChange | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.PodHomChainCtfDomains | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.ProperExceptionalRestriction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.ProperProductCounitTranspose | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.QbarPerverseSubcategories | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.QbarPerverseSupportCondition | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.RationalClosedSupportConstructible | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.RationalExceptionalRestriction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.RationalHomScalarTranspose | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.RationalRestrictionGlue | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.RationalTensorSymmetry | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.RelativeKunneth | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.RelativeProductInputDomains | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.RestrictionLocal | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.SfBidualityClass | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.SfPackageCoefficientDomains | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.SfPackageFieldOperationRealization | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.SitePerfectRationalBidual | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.SmoothPullbackSupportDimension | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.SystemScalarProjectionIdentification | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.TateTwistSupportCondition | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.TraceCorrespondences | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.VerdierCoefficientRealization | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.WeilChosenDualityExchange | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.CoefQbarVerdier | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.FiniteExceptional | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.FiniteScalarMateData | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.IntegralDualizing | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.IntegralVerdier | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.RationalOperations | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.RationalRetractEvaluation | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.RationalVerdier | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.ScalarSixCtf | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.ScalarSixDirectImage | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SixFunctors.WeilChosenDualityHom | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.SmoothPurity.NormalizedWitness | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.Targets.SmoothPurityQbar | Not adapted | Same proposition after unfolding; no source edit. |
| Sheaf.ZetaWeil.WeightPurityRoots | Not adapted | Same proposition after unfolding; no source edit. |
| TargetsCheck | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.PoincareDuality.Poincare | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.PoincareDuality.Verdier | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.SmoothPurity.Defs | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.Statement | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.Additivity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.Basic | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.BorelMoore | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.CoefficientMorphism | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.CompactCohomology | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.CompactPullback | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.Correspondence | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.CorrespondencePair | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.CurvePieces | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.Dualizing | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.FibreCoherence | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.FibreModel | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.FixedPoint | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.FixedPointScheme | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.Frobenius | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.GenericQuotient | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.HomologyUnit | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.KunnethVerdier | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.LefschetzVerdier | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.LocalTerm | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.LocalTermLocality | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.Main | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.ModelExtension | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.OpenSquare | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.PointNormalization | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.Product | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.ProperCompatibility | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.ProperCurve | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.ProperPushforward | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.PullbackFamily | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.RelativeFrobenius | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.Stalk | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.Statement | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.SupportedPairing | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.TraceClass | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.WeilBaseChange | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.TraceFormula.WeilTrace | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.WeilSheaf.Curve | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.WeilSheaf.EulerProduct | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.WeilSheaf.LFunction | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.WeilSheaf.RealPurity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.BettiSymmetry | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.DualityReciprocity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.Examples | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.FinalTheorems | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.HasseWeil | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.IntegralFactors | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.LissePurity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.Rationality | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.RealizationIndependence | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.RelativePurity | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.SmoothProper | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.TraceFormula | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.WeightSeparation | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.Weights | Not adapted | Same proposition after unfolding; no source edit. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | Not adapted | Same proposition after unfolding; no source edit. |

## Status

landed 20261025T051819-L-4142651 2026-10-25 (merge of deliver/C3/Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible)
