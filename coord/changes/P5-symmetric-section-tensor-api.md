# AlgebraicGeometry.SymmetricAlgebraSheaf.exists_sectionTensorEquiv

## Reason

The returned delivery duplicated this existing theorem because it was private. Expose the
original theorem in its unclaimed Sheaf module, import that module privately from the item,
and use the existing result. Its statement and proof stay identical. Add a source docstring.
Remove the duplicate `exists_sectionTensorEquivForGrading` and its two private congruence
helpers from the item. This implements the return for head 5ca6a902a38.

## Old

```lean
private theorem exists_sectionTensorEquiv {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] {U W : X.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hUW : U ≤ W) :
    letI : Algebra Γ(X, W) Γ(X, U) :=
      (X.presheaf.map (homOfLE hUW).op).hom.toAlgebra
    ∃ e : Γ(X, U) ⊗[Γ(X, W)] sections F (op W) ≃ₗ[Γ(X, U)] sections F (op U),
      ∀ (r : Γ(X, U)) (a : sections F (op W)),
        e (r ⊗ₜ[Γ(X, W)] a) = r • restriction F (homOfLE hUW).op a
```

## New

```lean
theorem exists_sectionTensorEquiv {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] {U W : X.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hUW : U ≤ W) :
    letI : Algebra Γ(X, W) Γ(X, U) :=
      (X.presheaf.map (homOfLE hUW).op).hom.toAlgebra
    ∃ e : Γ(X, U) ⊗[Γ(X, W)] sections F (op W) ≃ₗ[Γ(X, U)] sections F (op U),
      ∀ (r : Γ(X, U)) (a : sections F (op W)),
        e (r ⊗ₜ[Γ(X, W)] a) = r • restriction F (homOfLE hUW).op a
```

## Users

The only existing textual uses are the two internal calls in the comparison module.
They keep the same type and proof. The item adds one call to the newly accessible theorem.
The complete transitive downstream set from tools/downstream.py is listed below; making
an existing helper accessible introduces no type or data change for any consumer.
The adapted comparison module is unclaimed. No other group's module is edited.
No source-library module or target statement changes. Both modules compile in import order.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AbelianLevelCoarseModuli | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.AlgebraDirectedColimitFiniteType | T6 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.AlgebraicModuliStack | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.AlgebraicStackOpenDmLocus | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.AlterationCartierSubboundary | V8 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.BlowupReesSymmetricPresentation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra | P5 | Use the shared theorem in the base-change proof. |
| Sheaf.AlgebraicGeometry.CoarseModuliOpenRestriction | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CompleteFlagBundle | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ConormalConeHomExt | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ConormalConeZeroSectionPullback | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CoverNestedCartierPreparation | V9 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CurveProjectiveDenseCompletion | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CurveStackInfinitesimalDmLocus | S5 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.DMGeometricInertiaTrivial | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.DMIsomSpaceUnramified | K1 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.DmCoarseProperLocallyQuasiFinite | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.DmFiniteNormalizationCharts | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.DmOpenFiniteEtalePermanence | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.DmPointStabilizer | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.DmStackMorphismProperties | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ElementaryContractionEvaluation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantCurvePencil | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantFlatCurvePreparation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantMarkedPlurinodalFieldAlteration | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantSingleCurveNodalReduction | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantSmoothGaloisModel | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FieldCurveCompletionInsep | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingCompactSupportFiniteness | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FiniteStackSchemeTests | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FlatGradedTailProj | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FlatInertiaAlgebraicSpaceQuotient | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FormalModuliQuotient | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.GabberGlobalSNCAlteration | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.GloballyGeneratedProjectiveBundle | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.GoodCurvesGenericDiagram | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.HilbertUniformSectionBound | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse | S9 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.IntegralAlgebraDirectedColimitFinite | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothOpen | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback | G3 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.LogCanonicalDeletionAlgebra | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.MarkedNodalInfinitesimalFields | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ModuliChartNormalization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ModuliInertia | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ModuliIsoClassSheaf | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ModuliNormalizationTests | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ModuliStackProperties | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.NodalCurveStackSmooth | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.NodalTraitRegularization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.OpenModuliSubstack | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardRiemannRoch | R1 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PointBlowupFibreDefects | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PositiveCopyGradedQuotient | W7 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveAffineBaseBlowup | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChange | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChangeCoherence | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleComposition | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateGeometry | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateSubschemes | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleFrameModels | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry | X5 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleRankZero | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalData | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveStablePointedLevelParameter | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProperCurveAutomorphismScheme | T9 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProperFormalCurveAlgebraization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProperPairRadicialPreparation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProperRelativeAmpleProjectiveBundle | X7 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ReesConeNormalization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.RegularIdealConormalCoordinates | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.RelativeProjInvertibleTwist | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.RelativeProjectiveSpace | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.RelativeRegularIdealGeneration | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.RelativeTangentBundle | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.RelativelyVeryAmple | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.RepresentableFiniteStackProperties | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SectionIdealProjExpansion | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SectionReesNoetherianGeometry | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearSylowGoodComponents | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SmoothCurveAbelianLevelRigidification | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperFiniteCohomologyLocalSystem | W9 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SmoothSectionCentredCoordinates | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLift | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLiftingCriterion | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerObstruction | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryGradedRealization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryLeibniz | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedActionProjection | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedBoundaryProjection | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedPresentation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedProductProjection | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedQuotientMultiply | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorPowerBoundary | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.StableAbelianLevelNormalization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.StableFiberCurve | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.StableLevelVersalBranchFreeness | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.StablePointedCurve | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.StablePointedGenericExtension | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.StableVersalLevelChart | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.StackProperLocallyQuasiFiniteComposition | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineComparisonStalks | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineSectionComparison | unclaimed | Expose existing proved helper; its type and proof stay identical. |
| Sheaf.AlgebraicGeometry.SymmetricImagesModuleColimit | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts | J2 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorBoundaryKernelMapLocalMultiplication | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorBoundaryKernelMapNaturality | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorCoefficientActionOnSummand | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorCoefficientActionSupport | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorGradedActionKernelSecond | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorGradedActionKernelSecondDiagonal | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorGradedAlgebraData | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorGradedCoefficientSheafAction | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorGradedDegreeData | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorGradedKernelLocalIdeal | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorGradedKernelSquareZero | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorGradedQuotientActionHomogeneous | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorHomogeneousKernelAction | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorIdealSectionCoefficientComparison | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorIdealSectionLocalMultiplication | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorKernelSectionProduct | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TensorPowerAlgebraCoproduct | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.UnpointedLevelNormalizationProjectivity | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.UnramifiedDiagonalEtaleAtlas | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorBundleZeroSection | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletion | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletionData | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorProjectiveDehomogenization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorProjectiveFrameModel | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorProjectivePresentation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VectorTraceGeometry | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.tensorGradedAction_projection_first | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.tensorGradedAction_projection_second | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.DeligneLaumon.FiniteCompactSupportFibreSupportBound | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.AmplificationProper | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.CompletedConstructiblePreservation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.CompletedConstructibleReductionControl | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ConstructibleCompleteBaseChange | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.FiniteSmoothCanonicalInterfaces | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.IntegralFibreSectionSpecialization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.IntegralHenselianLisseSectionRigidity | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.IntegralLisseClosedBaseChange | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.KummerPartialNerveNaturality | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.LineZeroGeometry | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.OrientedProperImageConstructibility | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.P1KummerTraceSiteTransport | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PbcConstructibleReductionDirectImage | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PbcFiniteDirectImageCohomology | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PreservationConstructible | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ProperDirectImageFiniteness | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityConventions | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityNormalBundle | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityNormalCone | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityNormalProjection | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityRegularSection | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.PurityVectorBundleZeroSection | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.QbarCompactSupportBaseChange | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.QbarProperBaseChange | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.SectionCoordinateCounitNormalization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.SectionLocalDualizingComparisons | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.SectionNormalFibreMap | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.SectionReesBaseChangeEtale | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.AmpleNeighbourhood | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.BoundedDimensionProjectiveLocalModel | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.FiniteEtaModificationGluing | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.FiniteProjectiveEnvelope | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.LineQuotientHomogeneousFractionMap | N2 | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ProjectiveBundleProper | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ProjectiveBundleSeparated | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | No adaptation; existing signatures, definitions and proofs unchanged. |

## Status

landed 20261023T131711-L-2140364 2026-10-23 (merge of deliver/P5/Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra)
