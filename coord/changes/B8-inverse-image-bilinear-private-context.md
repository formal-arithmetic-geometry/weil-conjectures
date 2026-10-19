# CategoryTheory.site_inverse_image_bilinear_adjunction

## Reason

The stage-3 context scanner flags the new section-local `variable` command used by
private helpers. This record documents that context addition. The helper section
ends before the existing public theorem; its variables do not enter that theorem.
The transparency option is scoped to the private-helper section and the theorem
proof, and the unused-variable linter option is scoped to the existing theorem.
No declaration used by an importer changes its type or definition. All new helper
definitions in the existing module are private. No global instance, notation, or
attribute is registered. Public imports are identical. The new underlying-adjunction
module is imported privately for proofs, and its two public declarations have a new node.
No target statement or definition appearing in a target statement changes meaning.

## Old

The existing theorem signature, verbatim:

```lean
theorem site_inverse_image_bilinear_adjunction
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (u : C ⥤ D)
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map u ∈ K (u.obj X))
    (hpullback : ∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) u)
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
      J.toGrothendieck K.toGrothendieck).IsRightAdjoint]
    [PreservesFiniteLimits
      (u.sheafPullback (Type (max u₁ v₁ u₂ v₂ w)) J.toGrothendieck K.toGrothendieck)] :
    ∃ e : ∀ (F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (H : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}),
        SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G) H →
        SiteBilinearMap F G
          ((u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj H),
      (∀ (F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (H : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}),
        Function.Bijective (e F G H)) ∧
      (∀ (F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (H : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (β : SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G) H)
        (U : C) (x : F.obj.obj (Opposite.op U)) (y : G.obj.obj (Opposite.op U)),
        (e F G H β).app U x y = β.app (u.obj U)
          (siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u F U x)
          (siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u G U y)) ∧
      (∀ {F₀ F₁ G₀ G₁ : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}}
        {H₀ H₁ : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}}
        (a : F₀ ⟶ F₁) (c : G₀ ⟶ G₁) (h : H₀ ⟶ H₁)
        (β₁ : SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F₁)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G₁) H₀)
        (β₀ : SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F₀)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G₀) H₁),
        (∀ (V : D)
          (x : ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F₀).obj.obj (Opposite.op V))
          (y : ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G₀).obj.obj (Opposite.op V)),
          β₀.app V x y = h.hom.app (Opposite.op V)
            (β₁.app V
              (((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
                J.toGrothendieck K.toGrothendieck).map a).hom.app (Opposite.op V) x)
              (((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
                J.toGrothendieck K.toGrothendieck).map c).hom.app (Opposite.op V) y))) →
        ∀ (U : C) (x : F₀.obj.obj (Opposite.op U)) (y : G₀.obj.obj (Opposite.op U)),
          (e F₀ G₀ H₁ β₀).app U x y = h.hom.app (Opposite.op (u.obj U))
            ((e F₁ G₁ H₀ β₁).app U
              (a.hom.app (Opposite.op U) x) (c.hom.app (Opposite.op U) y)))
```

The original module has no private-helper section or section-local variables.

## New

The existing theorem has exactly the signature above. Added context for private
helpers (the nested section and the outer helper section both end before the theorem):

```lean
section

set_option backward.isDefEq.respectTransparency false

-- Private helpers with explicit parameters.

section RawMaps

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {F G H : Sheaf J AddCommGrpCat.{w}}

-- Private tuple and additivity helpers.

end RawMaps

-- Private bijectivity proof.

end
```

The theorem proof locally sets the same elaboration option; its declaration is
prefixed by `set_option linter.unusedVariables false in`. These options affect only
proof elaboration and linting. The existing `SiteBilinearMap` structure and
`siteAdjunctionUnitSection` definition are byte-for-byte unchanged.

## Users

The full transitive list from `tools/downstream.py` is recorded below. All retain
exactly the same existing public API; there are no forced adaptations. Text search
for `site_inverse_image_bilinear_adjunction` found no downstream use beyond its
own declaration in the baseline. Existing downstream uses of the bilinear-map
structure and unit-section definition are unaffected because those are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CompactProjectionExchange | W4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportProjectionOpenRestriction | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal | E4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericEvaluationCoherence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericImmersionProjection | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericStratumMate | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenProductExchange | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.EtaleGeometricBiduality | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | V3 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.KunBcKunnethCompat | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBound | K5 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | F6 | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| TargetsCheck | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Existing public declarations and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Existing public declarations and imports unchanged; no adaptation. |

## Status

landed 20261019T002509-L-2142139 2026-10-19 (merge of deliver/B8/Sheaf.CategoryTheory.Sites.InverseImageBilinearAdjunction)
