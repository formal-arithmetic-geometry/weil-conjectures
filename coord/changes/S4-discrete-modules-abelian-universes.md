# CategoryTheory.discreteModules_abelian and lifted group-ring equivalence

## Reason

The independent carrier universe w in the original theorem need not contain G.
The original enough-injectives claim is false at that size. The same obstruction was
already documented in the landed G3-discrete-continuous-injectives-universes change.
Take A = F_p and the profinite group G = product_K F_p, with K larger than the
carrier universe. If an injective I contained the trivial module F_p, let x be the
nonzero invariant image of 1. Each coordinate character chi_i gives the continuous
two-dimensional representation g(e1)=e1, g(e2)=e2+chi_i(g)e1. Injectivity extends
e1 -> x to a map into I. Its image y_i of e2 obeys (g-1)y_i=chi_i(g)x.
Distinct characters force distinct y_i, so K injects into I, impossible at the
prescribed size. All these two-dimensional representations have open stabilizers.

Use carrier max u w, which contains the group. Finiteness makes the coefficient
ring small in that universe regardless of v. The lifted group ring is then small,
and Mathlib's small-ring module theorem gives enough injectives. The existing
representation/group-ring construction works at every carrier universe: separate
its carrier universe w and coefficient-lift universe t, expose that proved general
form, and retain the original public equivalence as its specialization. This module
is unclaimed. This is not a use of the false independent-small-universe claim.

The source is Stacks injectives.tex, lemma-G-modules (Tag 04JF), whose group-ring
construction takes place in a universe containing the group. The finite coefficient
ring permits the sharper max u w bound rather than max u v w. Abelian structure,
module-detected exactness, and all topology/ring hypotheses stay identical.
The mathematical DAG statement has no independent-universe assertion; its Lean
attachment is corrected. No target signature or definition changes.

## Old

```lean
theorem discreteModules_abelian
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] :
    ∃ (h : Abelian (Rep.DiscreteContinuousRep.{v, u, w} A G)),
      discreteModuleActionProperties.{u, v, w} A G h
```

The existing public `Rep.representation_liftedGroupAlgebra_equivalence` has exactly
the following original signature (preserved verbatim):

```lean
theorem representation_liftedGroupAlgebra_equivalence
    (R : Type u) [Ring R] (G : Type v) [Group G] :
    Nonempty (Rep.{max u v w} R G ≌
      ModuleCat.{max u v w} (MonoidAlgebra (ULift.{w} R) G))
```

Its private construction had carrier `max u v w` and lift `w`.

## New

```lean
theorem discreteModules_abelian
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] :
    ∃ (h : Abelian (Rep.DiscreteContinuousRep.{v, u, max u w} A G)),
      discreteModuleActionProperties.{u, v, max u w} A G h
```

Added the following proved public generalization of the same explicit construction:

```lean
theorem representation_liftedGroupAlgebra_equivalence_anyUniverse
    (R : Type u) [Ring R] (G : Type v) [Group G] :
    Nonempty (Rep.{w} R G ≌ ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G))
```

## Users

All direct applications of `discreteModules_abelian` in the library already use
carrier `max u w`: ContinuousCochainsDeltaFunctor, ContinuousCochainsInvariantsZero,
ContinuousCochainsDerivedInvariants (two uses), and DiscreteContinuousCohomology.
Their instantiations reduce max u (max u w) to max u w, so every elaborated
consumer statement is identical. All four compile unchanged against the repair.
DiscreteContinuousFunctorialInjectives also compiles unchanged against the
generalized equivalence. No module held by another group is edited. Public imports
and the abbreviation discreteModuleActionProperties remain identical. All other
transitive users below only inherit these unchanged interfaces. The table records
all source import descendants of either changed module, plus the adapted module;
module ownership is read from coord/claims at preparation time.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.CurveOpenConstructibleGeneral | J4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral | Y7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EtaleModuleAffineBound | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | Q3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.KummerRootRegularDivisorPurity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.KunnethMapAgrees | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.OpenComplementKnown | G3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.OpenProductExchange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.ProperKunnethGlobalSections | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | S1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | E7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | K1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | K8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.CategoryTheory.DiscreteModulesAbelian | S4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.EtaleCohomology.KunnethOneProper | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | F9 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | C8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicPurityObjects | W9 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicSectionClosedSupport | Y5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.BoundaryDualizingComposition | Q8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | Q9 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | R5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CompactSupportCondensedRealization | U3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | R6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CompactificationLocalizing | F4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | Y9 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | J4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | R2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | U4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | Z5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ExceptionalFiniteRealization | Z6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | Z8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ExceptionalProEtaleRealization | Z9 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ExceptionalSiteRealization | A2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | C2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteCoefficientHomChange | M1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteComparisonLocalizing | V7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteConstructibleHom | M4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteProperLocalizing | W7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteStageVerdierBiduality | N4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteWindow | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteWindowBounded | C1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | X3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralConstructibleCompactness | E7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralConstructibleInternalHom | P1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralExceptionalInverseImage | M3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.InterchangeProperPasting | S4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.InternalHomPullback | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.KunBcKunnethCompat | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.LocalFrobeniusConjugacy | Q5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | A6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.MateOpenRestriction | U2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.MiddleExtensionHcZero | E5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.OpenComplementUnconditional | B3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PrimePowerTraitResidueModel | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperCoincidenceFrobenius | T6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperHeartBound | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | T7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurAdicReconstruction | H8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityAffineChartBounds | K5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityCoprojection | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | F1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityDncComparisons | G3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | E3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityDncInvariance | H2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityGysinStructure | F1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RationalStalkExact | A7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | Y6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.RestrictionLocal | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | T3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SfPreservationClass | K7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | M9 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SmoothMateCounitCancellation | G4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SmoothPurityMap | R2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SmoothTrace | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceCompactificationCohomology | U5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TraitResidueModel | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TwConventions | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.VerdierExchange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.WeilFourierInversion | J6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.WeilOne | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.WeilOpenImageDelta | E7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | S2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.WfTensorCompletionFrobenius | U8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | C1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | U2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.AugmentationCocycleComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.BaseFieldContinuousCochains | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.CoinducedContinuousAcyclic | K7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding | K8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.CompletedAugmentationAlgebra | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.ContinuousCochainsDeltaFunctor | K9 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.ContinuousCochainsDerivedInvariants | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.ContinuousCochainsInvariantsZero | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.ContinuousCochainsShortExact | M5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.DiscreteContinuousCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.DiscreteContinuousFunctorialInjectives | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.DiscreteContinuousInjectives | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.DiscreteIntegerInvariantsInfrastructure | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.DiscreteResolutionContinuousCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.DiscreteResolutionInhomogeneousCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.DvrGalois | Y2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.ProcyclicTwoTerm | E6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.RepresentationTheory.RepresentationLiftedGroupAlgebraEquivalence | unclaimed | Construction generalized; original public theorem signature preserved. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | V1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.ClassicalModuleAffineEvaluationBound | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | W2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.FiniteDualizing | M6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | M7 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.GeneratorReductionStatement | N3 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | K2 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.RationalVerdier | V4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | E4 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | P6 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | H1 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | X8 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | Y5 | No source adaptation; existing theorem applications retain the same specialized types. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| TargetsCheck | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Z8 | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | B4 | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.Statement | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | C1 | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | C3 | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | D2 | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No source adaptation; existing theorem applications retain the same specialized types. |

## Status

landed 20261019T093559-L-2329828 2026-10-19 (merge of deliver/S4/Sheaf.CategoryTheory.DiscreteModulesAbelian)
