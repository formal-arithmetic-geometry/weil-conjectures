# WeilConjectures.IntegralProjectionReduction.finiteIntrinsicProjectionCompatibility

## Reason

The assigned theorem was already marked STATEMENT-DISPUTED. It quantified over arbitrary,
independent tensor isomorphisms at all spaces. Its equation needs a tensor family compatible
with geometric inverse image and the actual adjunction units. For example, on a nonzero
projection over coefficients of odd characteristic, twisting the Y component by minus identity
while leaving the X component fixed changes one side only. Naturality in the two inputs at a
single space does not prevent that twist. The original universal assertion is not proved.

The repair specifies the existing balanced-tensor/K-flat construction, now exposed as an
explicit definition. It compares the proper and open/compositor factors separately and pastes
them. The only direct caller has an existential conclusion and now supplies this canonical
family; its public statement is verbatim unchanged. No Challenge target is changed. The
parent's intended meaning is preserved: the same finite projection has a compatible tensor
realization.

## Old

```lean
theorem finiteIntrinsicProjectionCompatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m))
    (e : ∀ X : SixFunctorSpace D,
        finiteIntrinsicDerivedTensor C.l E X.obj.left m ≅
          evaluatedTensor (C := C) (E := E) m X) :
      ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        (c : Compactification f.hom.left)
        (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
        (L : finiteTorConstructibleCategory C.l E (m + 1)
          (Nat.le_add_left 1 m) Y.obj.left)
        (U : normalizedDVRDerived C.l E X.obj.left m)
        (V : normalizedDVRDerived C.l E Y.obj.left m)
        (k : U ≅ K.obj) (l : V ≅ L.obj),
        SystemProjectionFormula.finiteProjection C.l E D C.different c
            X.obj.hom Y.obj.hom m U V ≫
          (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).map
            ((e X).hom.app (U, (finiteDerivedPullback C.l E m f.hom.left).obj V) ≫
              (evaluatedTensor (C := C) (E := E) m X).map
                (Prod.mkHom k.hom
                  ((finiteDerivedPullback C.l E m f.hom.left).map l.hom ≫
                    (S.finitePullback f).inv.app ⟨L.obj, L.property.1⟩))) ≫
          (S.finiteSupport f c).inv.app
            (((CompactSupportFiniteProjection.partialTensor S X).obj K).obj
              ((CompactSupportFiniteProjection.torPull S f).obj L)) =
        (e Y).hom.app
            ((sixFunctorFiniteSupport D C E (m + 1)
              (Nat.le_add_left 1 m) f c).obj U, V) ≫
          (evaluatedTensor (C := C) (E := E) m Y).map
            (Prod.mkHom
              ((sixFunctorFiniteSupport D C E (m + 1)
                (Nat.le_add_left 1 m) f c).map k.hom ≫
                (S.finiteSupport f c).inv.app K) l.hom) ≫
          (finiteInclusion (C := C) (E := E) m Y).map
            (CompactSupportFiniteProjection.component S f c K L)
```

The parent proof chose `e` from `finiteIntrinsicTensorRealization m S`, whose Nonempty
statement provides no geometric normalization, and applied the universal assertion to it.

## New

```lean
theorem finiteIntrinsicProjectionCompatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m)) :
      ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        (c : Compactification f.hom.left)
        (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
        (L : finiteTorConstructibleCategory C.l E (m + 1)
          (Nat.le_add_left 1 m) Y.obj.left)
        (U : normalizedDVRDerived C.l E X.obj.left m)
        (V : normalizedDVRDerived C.l E Y.obj.left m)
        (k : U ≅ K.obj) (l : V ≅ L.obj),
        SystemProjectionFormula.finiteProjection C.l E D C.different c
            X.obj.hom Y.obj.hom m U V ≫
          (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).map
            ((canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X).hom.app
              (U, (finiteDerivedPullback C.l E m f.hom.left).obj V) ≫
              (evaluatedTensor (C := C) (E := E) m X).map
                (Prod.mkHom k.hom
                  ((finiteDerivedPullback C.l E m f.hom.left).map l.hom ≫
                    (S.finitePullback f).inv.app ⟨L.obj, L.property.1⟩))) ≫
          (S.finiteSupport f c).inv.app
            (((CompactSupportFiniteProjection.partialTensor S X).obj K).obj
              ((CompactSupportFiniteProjection.torPull S f).obj L)) =
        (canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Y).hom.app
            ((sixFunctorFiniteSupport D C E (m + 1)
              (Nat.le_add_left 1 m) f c).obj U, V) ≫
          (evaluatedTensor (C := C) (E := E) m Y).map
            (Prod.mkHom
              ((sixFunctorFiniteSupport D C E (m + 1)
                (Nat.le_add_left 1 m) f c).map k.hom ≫
                (S.finiteSupport f c).inv.app K) l.hom) ≫
          (finiteInclusion (C := C) (E := E) m Y).map
            (CompactSupportFiniteProjection.component S f c K L)
```

The new definition `canonicalFiniteIntrinsicTensorComparison` is the actual scalar tensor
realization prewhiskered with the inverse coefficient equivalence, followed by cancellation
of both counits, uncurrying and `pullbackTensorFiniteModelIso`, in the inverse direction.
Its construction is the one already written in `FiniteIntrinsicTensorComponent`; it does not
choose an arbitrary isomorphism from an existence theorem. The two original existence-only
wrappers are no longer imported on this route; their declarations remain in the repository.

New coordinate definitions expose the fixed proper/open subwords and an explicit
midpoint comparison built from tensor, open, pullback and direct-image realization. It contains
no projection or inverse projection. Two new named theorem holes assert the separate proper
and open/compositor equations. Neither is the full compactification compatibility statement.

The adapted parent proof is:

```lean
  exact ⟨canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m,
    finiteIntrinsicProjectionCompatibility m S⟩
```

## Users

`tools/downstream.py Sheaf.Paper.FiniteIntrinsicProjectionCompatibility --uses
finiteIntrinsicProjectionCompatibility` found only the assigned module and its direct caller
as textual users of the changed declaration. The complete transitive importer list follows.
The adapted parent is unclaimed in the shared and current server records read for this work.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.CompactSupportProjectionCoherenceLaws | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FieldProjectionRefinementSquare | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FiniteIntrinsicProjectionRealization | unclaimed | Adapted proof chooses canonicalFiniteIntrinsicTensorComparison and applies the repaired theorem; signature and visibility unchanged. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FiniteProjectionIdentityNormalization | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | see claim record | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.IntegralProjectionFiniteEvaluation | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.IntegralProjectionReductionCoordinates | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.IntegralProjectionSystemEvaluation | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.IntegralStageProjectionStructuralIdentities | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.NormalizedIntegralTraceData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeDiamondEquality | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteCalculation | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteExpansion | see claim record | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPath | see claim record | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRightRouteCalculation | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeTransport | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.ProjectionFormulaCoherence | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.ProjectionIdentityAssembly | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RelativeKunneth | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | see claim record | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TensorHomExchange | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TransportIntegralCounitRealization | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No use of the changed declaration; parent public conclusion is unchanged. |

The assigned module adds a public import of the canonical comparison because its statement
names that definition. New definitions use public imports needed by their bodies; proof-only
factor imports remain private. Existing public imports and declaration signatures of the
adopted WeilConjectures tree are unchanged.

## Status

landed 20261028T055622-L-778192 2026-10-28 (merge of deliver/C3/Sheaf.Paper.FiniteIntrinsicProjectionCompatibility)
