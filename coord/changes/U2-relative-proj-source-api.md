# AlgebraicGeometry.exists_relativeProjData

## Reason

Complete the assigned 2026-10-17 duplicate repair. The previous F3 delivery closed the
hole with a second gluing construction but retained the duplicate theorem and its sole
consumer. This delivery removes that second construction and derives the consumer's
construction from the existing source-library relative Proj.

`RelativeProjAlgebra.affineData` packages the actual section rings, homogeneous image
submodules and restriction maps. Its coefficientwise base change is proved using the
existing total-section base-change theorem and direct-sum decomposition. The source
`relProjGluingData` supplies the scheme and structure map. Identity-on-sections grading
isomorphisms and the source preimage theorem supply the existing `RelativeProjData` fields.
No data come from an arbitrary existence witness. The formerly private grading
comparisons are now documented public bridge data, so no private helper occurs in a
public definition. Existing source files and source declarations are unchanged.

## Old

The item publicly imported `Sheaf.AlgebraicGeometry.RelativeProjData` and declared:

```lean
theorem exists_relativeProjData {X : Scheme.{u}} (A : RelativeProjAlgebra X) :
    ∃ D : RelativeProjData A,
      ∀ (P : Scheme.{u}) (π : P ⟶ X)
        (i : ∀ V : X.affineOpens, (π ⁻¹ᵁ V.1).toScheme ≅ A.localProj V),
        (∀ V : X.affineOpens,
          (i V).hom ≫ A.localBase V ≫ V.1.ι = (π ⁻¹ᵁ V.1).ι ≫ π) →
        (∀ (V W : X.affineOpens) (h : W ≤ V),
          (i W).inv ≫ P.homOfLE (π.preimage_mono h) ≫ (i V).hom =
            A.localTransition h) →
        ∃! e : D.proj ≅ P,
          e.hom ≫ π = D.π ∧
            ∀ V : X.affineOpens,
              (D.restrictionIso V).inv ≫ (D.π ⁻¹ᵁ V.1).ι ≫ e.hom =
                (i V).inv ≫ (π ⁻¹ᵁ V.1).ι
```

Its private `chartFunctor`, `chartGluing`, `chartIso`, `construction` and helper instances
implemented another relative gluing and colimit comparison.

The sole consumer publicly imported `Sheaf.AlgebraicGeometry.RelativeProjExists` and used:

```lean
def construction : RelativeProjData (algebra X r) := (exists_relativeProjData (algebra X r)).choose
```

`RelativeProjAffineRestriction` kept `sectionAlgebra`, `grade`, `gradeRing`, `toGrade`,
`fromGrade`, the two irrelevant-ideal lemmas, `gradeIso` and `gradeIso_hom_base` private.
Its pullback proof independently assembled the affine Proj base-change square.

## New

The obsolete item is withdrawn under steps 8b/8d. Its path is listed in
`deleted.txt`, and the delivery lands the standard empty module. Source Basic
is publicly imported by the retained affine-data bridge, and the only old
consumer imports that bridge. The replacement argument and parent migration
are included in this delivery.

The consumer publicly imports `Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction` and uses:

```lean
def construction : RelativeProjData (algebra X r) := (algebra X r).realization
```

The new bridge signatures in `AlgebraicGeometry.RelativeProjAlgebra` are:

```lean
noncomputable def affineData : X.GradedAlgebraData
noncomputable def realization : RelativeProjData A
```

The first uses the now-public grading comparisons listed above; `gradeRestriction` is
actual section restriction and `gradeRestriction_baseChange` proves its coefficientwise
base change. `gradeIso_naturality` gives transition compatibility. `affineRestrictionIso`
and `affineRestrictionIso_hom_ι` identify the source chart with the inverse-image open.
`realization.gluing` is exactly `A.affineData.relProjGluingData`. Its equations are
proved from the source restriction API. The existing three local-transition theorem
signatures are unchanged; `localTransition_isPullback` now uses that source API.

The represented relative projective scheme changes from an existence-selected realization
to the explicit canonical one. Both have exactly the same local models, base maps,
transition maps and chart compatibility. This does not strengthen or weaken any
mathematical statement. No Challenge target statement uses the changed definitions.

## Users

`tools/downstream.py ... --uses AlgebraicGeometry.exists_relativeProjData` finds only the
item and `RelativeProjectiveSpace`. A full textual search of both Lean roots confirms
there are no further references and no other direct importers. The table is the union
of the full downstream lists of the bridge and the consumer; the direct importers of
the changed consumer are checked against the adapted construction. Four compile; four
checks stop at independent dependency/build-artifact failures detailed in report.md.
The edited direct user itself compiles cleanly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompleteFlagBundle | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.GloballyGeneratedProjectiveBundle | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChangeCoherence | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateGeometry | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateSubschemes | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleFrameModels | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleRankZero | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalData | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction | unclaimed | Explicit affine-data and realization bridge; original public results retained. |
| Sheaf.AlgebraicGeometry.RelativeProjExists | unclaimed | Withdrawn under steps 8b/8d; source replacement and parent migration supplied. |
| Sheaf.AlgebraicGeometry.RelativeProjectiveSpace | unclaimed | Import and construction body adapted; signatures retained. |
| Sheaf.AlgebraicGeometry.RelativelyVeryAmple | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletion | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletionData | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.VectorProjectiveDehomogenization | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.VectorProjectiveFrameModel | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.AlgebraicGeometry.VectorProjectivePresentation | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.AmpleNeighbourhood | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.BoundedDimensionProjectiveLocalModel | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.FiniteProjectiveEnvelope | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.ProjectiveBundleProper | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| TargetsCheck | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Transitive consumer; no reference to the removed theorem; existing signatures retained. |

## Status

landed 20261021T233802-L-862758 2026-10-21 (merge of deliver/U2/Sheaf.AlgebraicGeometry.RelativeProjExists)
