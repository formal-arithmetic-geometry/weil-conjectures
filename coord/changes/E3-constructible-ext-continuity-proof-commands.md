# AlgebraicGeometry.ProEtale.CondensedRing.constructibleExtContinuityStratum

## Reason

The proof adds private qcqs costalk and finite-free Hom helpers. The static delivery
check treats their enclosing namespace, opens, local instance registrations and the
file-level elaboration setting as command changes requiring a change record. All
public imports, existing declaration signatures and visibility stay identical. No
public definition, global instance or target meaning changes. The two colimit helper
registrations are explicitly local to the namespace; the high heartbeat settings are
scoped to individual private lemmas. The new open only resolves names in this file.
No importer requires adaptation.

## Old

The existing statement, retained verbatim:

```lean
theorem constructibleExtContinuityStratum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {S Z V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : V ⟶ X) (uS : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion uS] [QuasiCompact uS]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hΛ : IsAdmissibleCoefficient Λ)
    (L : supportModules Λ S) (hL : ProEtale.IsLisseCoefficientModule Λ L)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (supportModules Λ X) ℤ)
    (b : ℤ) (hK : ∀ (t : I) (n : ℤ), n < b → IsZero ((K.obj t).X n)) (q : ℤ) :
    IsIso (colimit.post K
      (DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory (supportModules Λ X)) q ⋙
        preadditiveCoyoneda.obj
          (op ((DerivedCategory.singleFunctor (supportModules Λ X) 0).obj
            ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ uS).obj L))))))
```

Original file commands:

```lean
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
```

## New

The theorem has exactly the statement and visibility recorded above, with a complete
proof and no new holes. Additional proof-local commands are:

```lean
set_option backward.isDefEq.respectTransparency true
open CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.ProEtale
attribute [local instance 2000] moduleColimits
attribute [local instance 2000] complexColimits
```

The private helpers end before the original public namespace resumes. Each expensive
private lemma additionally scopes `maxHeartbeats`, `synthInstance.maxHeartbeats` and
`synthInstance.maxSize` using `set_option ... in`. The preserved admissibility binder
uses a declaration-scoped unused-variable linter setting. These affect elaboration of
the delivered proof, not public statements or constructions.

## Users

The successful `tools/downstream.py` run found 253 transitive importers and one direct
importer, `Sheaf.Paper.ConstructibleExtContinuity`. With `--uses` and the public theorem
name, there was no downstream textual use of that declaration yet. The inventory was
checked again against current source import lines. The table lists every transitive
importer and its current claim holder (255 rows in the source check). All public imports and signatures are unchanged,
so each retains the same mathematical meaning and no file is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Identical public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Identical public interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Identical public interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Identical public interface; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | Identical public interface; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | H5 | Identical public interface; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Identical public interface; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Identical public interface; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Identical public interface; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | E4 | Identical public interface; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Identical public interface; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Identical public interface; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Identical public interface; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | U7 | Identical public interface; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | Identical public interface; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | U8 | Identical public interface; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | C5 | Identical public interface; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Identical public interface; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Identical public interface; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Identical public interface; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | G7 | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteWindow | W5 | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | C1 | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | Identical public interface; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | K4 | Identical public interface; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | M1 | Identical public interface; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | W8 | Identical public interface; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | M2 | Identical public interface; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | E9 | Identical public interface; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | Identical public interface; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Identical public interface; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Identical public interface; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Identical public interface; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Identical public interface; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Identical public interface; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Identical public interface; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Identical public interface; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Identical public interface; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Identical public interface; no adaptation. |
| Sheaf.Paper.ProperHeartBound | K5 | Identical public interface; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Identical public interface; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Identical public interface; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Identical public interface; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Identical public interface; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Identical public interface; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Identical public interface; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Identical public interface; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Identical public interface; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Identical public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Identical public interface; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | X9 | Identical public interface; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Identical public interface; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Identical public interface; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Identical public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Identical public interface; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | Identical public interface; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Identical public interface; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Identical public interface; no adaptation. |
| TargetsCheck | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.Statement | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Identical public interface; no adaptation. |

The two-file `lcompile.py --all` consumer check compiled the delivered module in
41.5 seconds and the unchanged direct importer in 4.5 seconds, with no errors or
warnings. The original public signatures and public imports match byte for byte.

## Status

landed 20261019T002531-L-2149172 2026-10-19 (merge of deliver/E3/Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum)
