# CategoryTheory.Mod.monoidalClosed and CategoryTheory.Mod.hasFunctorialFlatResolution

## Reason

Fill the two existing instance holes without changing their signatures, attributes or public
imports. All added helpers are proved and private. The private proof imports are InternalHom
and TensorRegular in WeilConjectures.CategoryTheory.Monoidal.Mod.

Closedness follows from the existing concrete equalizer adjunction, transported along the
coequalizer tensor comparison and symmetry. The exposed instance chooses an adjoint of this
proved left adjoint; its supporting Prop proof is abstracted privately by Lean. No private data
helper enters the exposed definition. Adjoint functors are determined up to natural isomorphism.

The resolution is constructed from the supplied ambient resolution, using the explicit functor
forget R followed by its flat resolution and free R, with augmentation free(pi) followed by the
counit. Its values are flat by the split free-tensor coequalizer and reflection of finite limits.
The ambient resolution is supplied by a hypothesis, not an unproved existence theorem.

The original module/declaration docstrings and original open commands remain verbatim. Two
local helper sections open MonObj only inside those sections. There are no public additions,
changed statements, forced consumer adaptations, or new holes. Filling the intended structures
does not change any target's mathematical meaning; the data instance is included for review.

## Old

```lean
noncomputable instance monoidalClosed : MonoidalClosed (Mod C R) :=
  sorry

instance hasFunctorialFlatResolution [Abelian.HasFunctorialFlatResolution C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) :=
  sorry
```

## New

```lean
noncomputable instance monoidalClosed : MonoidalClosed (Mod C R) :=
  ⟨fun M ↦
    have : (MonoidalCategory.tensorLeft M).IsLeftAdjoint := by
      exact relativeTensor_isLeftAdjoint M
    ⟨_, Adjunction.ofIsLeftAdjoint (MonoidalCategory.tensorLeft M)⟩⟩

omit [MonoidalPreadditive C] in
instance hasFunctorialFlatResolution [Abelian.HasFunctorialFlatResolution C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) := by
  classical
  -- Preserve the original interface: no monoidal additivity is required here.
  rename_i hAdd hSymm hClosed hMon hComm hResolution
  clear hAdd
  have : (free R).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (freeForgetAdjunction R)
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  let P := forget R ⋙ Λ.F ⋙ ObjectProperty.flat.ι ⋙ free R
  let π : P ⟶ 𝟭 (Mod C R) :=
    Functor.whiskerRight (Functor.whiskerLeft (forget R) Λ.π) (free R) ≫
      (freeForgetAdjunction R).counit
  refine ⟨{ F := ObjectProperty.lift _ P (fun M ↦ flat_free (Λ.F.obj M.X).property)
            π := π
            epi_π_app := ?_ }⟩
  intro M
  change Epi ((free R).map (Λ.π.app M.X) ≫ (freeForgetAdjunction R).counit.app M)
  have : Epi (Λ.π.app M.X) := inferInstance
  have : Epi ((free R).map (Λ.π.app M.X)) := (free R).map_epi _
  have : Epi ((freeForgetAdjunction R).counit.app M) := by
    have : IsSplitEpi ((forget R).map ((freeForgetAdjunction R).counit.app M)) :=
      ⟨⟨(freeForgetAdjunction R).unit.app M.X,
        (freeForgetAdjunction R).right_triangle_components M⟩⟩
    exact (forget R).epi_of_epi_map inferInstance
  infer_instance
```

## Users

The source-only downstream.py --uses scan reports 372 transitive importers. The textual uses of
monoidalClosed are ProEtalePullbackInternalHom, CondensedOpenExtensionProducts,
IntegralResidueTensorRouteModel and InternalSliceDerivedHomComparison (besides the item).
There are no textual external uses of hasFunctorialFlatResolution. Implicit instance consumers
retain exactly the same type-class interfaces. No consumer needs an adaptation. The free-counit epimorphism is proved directly from the split
underlying counit; importing FreePresentation for this would add a MonoidalPreadditive hypothesis
that the original elaborated instance does not have. The delivered proof avoids that change. It omits and clears the unused monoidal-additivity
instance from the proof context, so opportunistic instance synthesis cannot add that hypothesis.
The final elaborated signatures, including universes, match the published original signatures.
An import-level test infers flat resolutions without monoidal additivity; the unchanged
Grothendieck-abelian instance is tested separately with the additivity hypothesis.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KFlatModuleObject | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearActionRigidity | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearTraceAction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearUniversalAction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLineLocalization | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLinePurity | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleDevissage | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleLocalizingClosure | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorPreservation | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexCompatibility | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedModulePullbackExact | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedQbarPointBasis | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisPushforward | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisSections | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisUnit | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisUnitOfSections | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedScalarRealization | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingCohomologicalRepresentability | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.LfpTensorSingle | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.LocallyFreeTensorSingle | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleObjectPostnikovRoos | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteLocallyProjective | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteProjectiveDualizable | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleObjectProductsExact | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtalePullbackInternalHom | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingSheafClosedLocalization | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedReconstruction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.SfFullcdUsedClass | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.CategoryTheory.InternalSectionModuleFlat | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentLisse | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CoefficientHeartCommonStratification | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseRestriction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CoefficientHeartOrderedRefinement | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CoefficientHeartSmall | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CoefficientHeartStratificationDefs | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ComapUpperStarIsoComposition | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ComapUpperStarIsoMate | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CompletedCondensedCoefficients | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CompletedDirectImageLimits | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CompletedProjectionCoherence | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CompletedPullbackUnitTower | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CompletedTowerCorners | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ComponentRelativeProfiniteSite | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedAmbientExchange | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedCoefficientFamilyHomStage | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedCoefficientHomStage | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedCoefficientIsoConstructible | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedCoefficientPointUnitPasting | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedConstantConstructibility | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedConstructibleGenericLfp | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedConstructiblePiece | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFiniteFreeDerivedHom | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFiniteFreeHomContinuity | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFiniteFreeHomEvaluation | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFiniteFreeInternalHomColimits | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFiniteFreeTensorExact | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelImmersionRestriction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationMatrices | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedFpHomStage | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedHypercoverComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedHypercoverInjectiveRow | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedInternalHomSections | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedLocalCoefficientAdjoints | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedLocalPresentationPullback | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedPiece | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedModuleDerivedPushpull | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedOpenExtensionProducts | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedOverlapFactorTranspose | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedPointBasisEvaluation | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpCoverComposition | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedQcqsPushforwardLocalComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedSurjectiveClosedEquivalence | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedSurjectiveClosedLocalPresentation | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedUnderivedPushforwardContinuity | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CondensedZlReduction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ConstantModelTorAmplitude | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousAlgClConstructibleTor | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousAlgClLocalFree | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralCoefficientTelescope | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralCoefficients | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralDerivedUnit | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralScalarExact | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersection | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousPresentationFiberCompatibility | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ContinuousRingUniverseRealization | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.DivisibleExtensionDerivedReduction | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FiniteLevelProEtaleBaseChange | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FiniteLevelRectangle | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FormalClosedPullbackProducts | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FourArrows | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.GeoCartierExponentIndependence | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.GeometricFieldProEtaleEvaluation | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeartClosure | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralContinuousCokernelLocalModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralContinuousPresentationMatrix | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralLfpConstantModelComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralReductionScalar | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralReductionTensor | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralReductionTriangulatedProperty | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueComparisonInterface | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueDerivedMonoidal | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueOrdinaryMonoidal | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueOrdinaryRestrictPullComp | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueOrdinaryTensorNormalization | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueOrdinaryTensorSquare | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResiduePerfect | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResiduePullFlatModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResiduePullFlatModelComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResiduePullFlatModelMateNormalized | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResiduePullOrdinaryUnit | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResiduePullSquare | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResiduePullSquareComp | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResiduePullSquareData | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResiduePullSquareIsIso | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResiduePullbackPreservesFlat | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueRestrictPullComp | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarCounitModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorPresentation | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorPullCounitCore | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorRouteDescent | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.InternalSectionDerivedTensorComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.InternalSectionTotalComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.InternalSliceDerivedHomComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.InverseImageModuleFlat | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IsomorphismReductionTower | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.LisseFiniteCoefficientModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.LisseFiniteHomLift | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.LocalizingAdmissibleCoefficients | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.LocalizingClosure | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.LocalizingClosureExistence | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ModuleObjectProjectionMap | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ModuleProjectionSectionArrows | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ModuleProjectionSectionComposites | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ModuleProjectionSectionInverse | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ModuleSectionProjectionArrow | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.OpenPullbackGenerators | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.PerfectProjectionFormula | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ProEtaleConstantReductionTower | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ProfinitePointPullback | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ProjectionFormulaBaseChangeNaturality | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ProjectionFormulaIdentityCompactification | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ProperBaseChangeFourArrows | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.PullbackFiniteConstantLocalModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.PurInverseImageTensorComparison | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.PurInverseImageTensorHom | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.RefinementBoundaryVanishing | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.SplitProEtaleModuleProductMap | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.StratumAmbientHom | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.StratumScalarExtension | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.TateInverseLimitBaseChange | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.UnboundedLocalizingPullback | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.PoincareDuality.CompatibleIntegralRootBases | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.PoincareDuality.ConstructibleShiftSingle | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.PoincareDuality.IntegralResidueLimit | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.PoincareDuality.IntegralResidueQuotient | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.PoincareDuality.IntegralTateBasis | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.PoincareDuality.IntegralTateLocalLine | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.PoincareDuality.TateTwistLocalLine | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SecSmoothPurity.DirectImageScalarExchange | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarExchange | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SecSmoothPurity.OrdinaryRestrictionPullbackSquare | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SecSmoothPurity.TensorPullbackSquare | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SixFunctors.AdmissibleDirectImage | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SixFunctors.AdmissibleTensorConstructibility | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesStructural | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleEmbedding | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.TateTwist.ProEtale | unclaimed | Same signatures and public imports; no adaptation. |

## Status

landed 20261020T174843-L-809917 2026-10-20 (merge of deliver/S5/WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian)
