# AlgebraicGeometry.ProEtale.RationalP1.diagonalTensorMap

## Reason

The direct composite forces Lean to compare large concrete projective-line module-site
instances when its naturality proof is specialized. Profiling isolated this conversion:
the arbitrary-scheme naturality lemmas compile in about 30 seconds, while the concrete
body conversion and attempts to generalize it exceeded 120 seconds. The repair defines
that identical composite once over arbitrary schemes as `sectionTensorMap`, then applies
it to the existing canonical diagonal, first projection, section comparison and unit
comparison. No existence witness is introduced and no datum is selected arbitrarily.
The helper is explicit projection-map/section/unit composition, marked irreducible like
the original map. This preserves the blueprint construction, including its orientation.

All existing theorem signatures, universes, attributes and public imports are unchanged.
The definition data and hence the interpretation of every downstream statement remain
the same. Target statements are untouched; review of any target whose definitions use
this map must verify this same-composite identification. No source-library file changes.

## Old

```lean
@[irreducible]
def diagonalTensorMap (Y : Scheme.{u}) (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗
      (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
        (unit Λ (ProjectiveLine Y)) ⟶
      (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj M :=
  projectionMap Λ (diagonalImmersion Y) _ _ ≫
    (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).map
      (tensorHom ((pullSectionIso Λ Y (firstProjection Y) (pullback.diagonal_fst _)).hom.app M)
        (singleUnitIso Λ (ProjectiveLine Y)).hom ≫ (ρ_ M).hom)
```

## New

```lean
@[irreducible]
def sectionTensorMap {X S : Scheme.{u}} (g : X ⟶ S) (p : S ⟶ X)
    (s : moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g ≅
      𝟭 (DerivedCategory (Modules Λ X)))
    (U : DerivedCategory (Modules Λ X)) (e : U ≅ 𝟙_ (DerivedCategory (Modules Λ X)))
    (M : DerivedCategory (Modules Λ X)) :
    (moduleObjectDerivedPullback Λ p).obj M ⊗
      (moduleObjectDerivedPushforward Λ g).obj U ⟶
        (moduleObjectDerivedPushforward Λ g).obj M :=
  projectionMap Λ g _ _ ≫ (moduleObjectDerivedPushforward Λ g).map
    (tensorHom (s.hom.app M) e.hom ≫ (ρ_ M).hom)

@[irreducible]
def diagonalTensorMap (Y : Scheme.{u}) (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗
      (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
        (unit Λ (ProjectiveLine Y)) ⟶
      (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj M :=
  sectionTensorMap Λ (diagonalImmersion Y) (firstProjection Y)
    (pullSectionIso Λ Y (firstProjection Y) (pullback.diagonal_fst _))
    (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M
```

## Users

`tools/downstream.py Sheaf.Paper.RationalP1DiagonalTensor --uses diagonalTensorMap`
reports only the item itself as a textual user of the changed definition. The only
external use of the associated inverse is `diagonalClassMap` in
`Sheaf.Paper.RationalP1AmbientComposites`; it composes `diagonalTensorIso.hom` and does
not unfold the repaired definition. Its signature and mathematical composite are
unchanged. All transitive importers reported by the tool are listed below. No other
module needs adaptation. Empty schemes and zero coefficient modules remain admissible;
the parametric constructor simply composes the supplied morphisms in those cases too.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.RationalP1DiagonalTensor` | X3 | Factor the same canonical map and prove inverse naturality; all existing signatures preserved. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.DeligneLaumon.GeometricConstituentOrbit` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.DeligneLaumon.GeometricCurveDiagramDescent` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.DeligneLaumon.MarkedGeometricCurveModel` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.DeligneLaumon.PairEigenvalueCurveTest` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.DeligneLaumon.PairEigenvalueGeometricConstituent` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.DeligneLaumon.SemisimpleFrobeniusOrbitDescent` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.DeligneLaumon.SmoothAffineConstituentPurity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.AdicProperLocalizingAdjunctionComparison` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.AffineLineAdjunctionAssembly` | U6 | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalCounitRepresentation` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalRealizationProperties` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstruction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstructionData` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalRefinementCounits` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalSystemRecognition` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedHomChainRealization` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedOpenCoefficientModels` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitComparisons` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitRealization` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitRealizationSupport` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitUnits` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CondensedOpenUnitComparison` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.DetThmSfCtfStabilityInternalHom` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralMaps` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.ExceptionalRealizationNormalization` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.FinitePurityCounitSystem` | S3 | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.OrientationScalarTowerTransport` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.RationalAffineAdjunctionCalculus` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.RationalAffineTensorCalculus` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.RationalP1AmbientComposites` | unclaimed in mirror | Uses diagonalTensorIso.hom in diagonalClassMap; its type and canonical map are unchanged; no adaptation. |
| `Sheaf.Paper.RationalP1KernelContractions` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.RationalP1Triangle` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.RationalP1UnitCounit` | J4 | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.RestrictionLocal` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.SmoothPurityBaseChangeFactors` | M4 | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.TensorHomCoefficientTransposes` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.TowerGeometricPurityMate` | M2 | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.VerdierHomChainComposition` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.VerdierHomChainCompositionData` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.VerdierIdentityProjection` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.VerdierOrdinaryTensorTransport` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.VerdierProjectionExceptionalPaste` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.PoincareDuality.ConstructibleSheafBiduality` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | C8 | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionNaturality` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSquare` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransitionData` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.IntegralAffinePurityInduction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.IntegralKernelContractions` | D4 | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.IntegralKernelUnitCounit` | Y6 | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.IntegralProjectiveLineAdjunction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.ScalarCompositeModelPasting` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.ScalarDenseRefinementSquare` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.ScalarRefinementClosureSquare` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.ScalarSixCompactSupport` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SixFunctors.ScalarSixDirectImage` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `TargetsCheck` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.Statement` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.Additivity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.BaseChangeCoherence` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.BorelMoore` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.CoefficientMorphism` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.CompactCohomology` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.CompactPullback` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.Correspondence` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.CorrespondencePair` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.CurvePieces` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.Dualizing` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.FibreCoherence` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.FibreModel` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.FixedPoint` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.FixedPointScheme` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.Frobenius` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusLocalTerm` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.GenericQuotient` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.HomologyUnit` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.KunnethVerdier` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.LefschetzVerdier` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.LocalTerm` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.LocalTermLocality` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.Main` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.ModelExtension` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.OpenPieceCoherence` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.OpenSquare` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.PointNormalization` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.Product` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.ProperCompatibility` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.ProperCurve` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.ProperPushforward` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.ProperPushforwardKernel` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.PullbackFamily` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobenius` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobeniusComparison` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobeniusIterate` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionInduction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.Stalk` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.SupportedPairing` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.TraceClass` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.TraceClassAdditivity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.WeilBaseChange` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.WeilSheafUpperStar` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.TraceFormula.WeilTrace` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |
| `WeilConjectures.ZetaFunction.WeilObjectComparison` | unclaimed in mirror | Transitive importer; no textual use of diagonalTensorMap or unfolding of its body; no adaptation. |

## Status

landed 20261026T071447-L-3934752 2026-10-26 (merge of deliver/X3/Sheaf.Paper.RationalP1DiagonalTensor)
