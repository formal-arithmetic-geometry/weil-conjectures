# unrestrictedIntegralReductionExistence

## Reason

Comparing separately named copies of the universal scalar-extension witness inside
complexes expands tensor/sheafification instances and exceeds the single-file limit.
Share the already existing scalarReductionExistence and scalarReductionExtension.
The old and new terms are definitionally equal: the witness is exactly the same
universal change-of-rings theorem with the same standard localizations and arguments.
All public signatures, transitions, tensor generators and localization instances stay
identical. The module is unclaimed. No source-library declaration is modified.
The new public import supports the shared definition bodies.

## Old

```lean
noncomputable def unrestrictedIntegralReductionExistence (n : ℕ) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)))
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (O := completedIntegralCommRingSheafUnrestricted l E Y)
    (O' := integralCoefficientCommRingSheaf l E Y n)
    (completedIntegralCommRingProjectionUnrestricted l E Y n)
```

```lean
noncomputable def unrestrictedIntegralReductionFunctor (n : ℕ) :
    integralTowerModules l E Y ⥤
      SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n) :=
  (unrestrictedIntegralReductionExistence l E Y n).choose
```

```lean
noncomputable instance unrestrictedIntegralReductionFunctor_additive (n : ℕ) :
    (unrestrictedIntegralReductionFunctor l E Y n).Additive :=
  (unrestrictedIntegralReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose
```

```lean
noncomputable def unrestrictedIntegralTensorSection (n : ℕ)
    (M : integralTowerModules l E Y)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U) (x : M.val.obj U) :
    ((unrestrictedIntegralReductionFunctor l E Y n).obj M).val.obj U :=
  (eqToHom ((unrestrictedIntegralReductionExistence l E Y n).choose_spec.choose M).symm).val.app U
    ((CategoryTheory.toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjectionUnrestricted l E Y n) M).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
            ((completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U).hom] x))
```

## New

```lean
noncomputable def unrestrictedIntegralReductionExistence (n : ℕ) :=
  scalarReductionExistence l E Y n
```

```lean
noncomputable def unrestrictedIntegralReductionFunctor (n : ℕ) :
    integralTowerModules l E Y ⥤
      SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n) :=
  scalarReductionExtension l E Y n
```

```lean
noncomputable instance unrestrictedIntegralReductionFunctor_additive (n : ℕ) :
    (unrestrictedIntegralReductionFunctor l E Y n).Additive :=
  scalarReductionExtensionAdditive l E Y n
```

```lean
noncomputable def unrestrictedIntegralTensorSection (n : ℕ)
    (M : integralTowerModules l E Y)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U) (x : M.val.obj U) :
    ((unrestrictedIntegralReductionFunctor l E Y n).obj M).val.obj U :=
  (eqToHom ((scalarReductionExistence l E Y n).choose_spec.choose M).symm).val.app U
    ((CategoryTheory.toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjectionUnrestricted l E Y n) M).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
            ((completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U).hom] x))
```

The private object/map equations explicitly change to the shared witness before
applying its specification. Local irreducibility protects concrete tensor internals.
The existing definition node is def-weil-integral-reduction-tower; its mathematical
statement and Lean attachment remain valid. Since the terms are definitionally equal,
target meanings do not change. Definition-sensitive review is requested for every
reached target that uses this construction, as required by AGENTS.md section 4.
The independent reader should verify the definitional equality. All five `rfl`
checks in `scratchpad/retained-profile-checks/OperationRestoredInterfaceCheck.lean`
compiled successfully (19.3 seconds). The source category keeps its original
body so that existing generated proof constants remain available.

The complex functor `unrestrictedIntegralComplexFunctor` keeps its original
body, including `unrestrictedIntegralFiniteComplex` and the explicit restriction
of scalars. Consumers that keep the finite reduction functor irreducible therefore
retain their literal finite-complex and underlying-sheaf endpoints. No consumer
source change is included.

The termwise finite reduction `unrestrictedIntegralFiniteComplex` changes from
`noncomputable abbrev` to `@[reducible] noncomputable def`, with signature and
body verbatim. It is still the same ordinary scalar extension applied degreewise.

## Users

Source scan refreshed 2026-10-26T08:59+00:00.
The import closure has 2012 modules; 101 mention the changed
declarations under the `tools/downstream.py --uses` criterion.
Statements, module actions and constructions remain definitionally equal.
No forced consumer edits are included.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.AdicRoosRealizationReductions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.AdicScalarFlatReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.BalancedFiniteTowerGeneratorComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.BalancedFiniteTowerKoszulAugmentation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.BalancedFiniteTowerQuotientComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.BalancedFiniteTowerScalarComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ClopenCompletedOperationTowers` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientSequenceRoosModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoherentQuotientReductionComparison` | K8 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompleteResidueCohomologyBounds` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedCoefficientPushforwardModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedPerfectScalarPullback` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedPrimitiveCounitComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | E4 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedPullbackUniverseTransportData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedTensorScalarLinearity` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitOrdinaryAdjunction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitStrictQuotientModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ConstantScalarStrictUnit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.EffectiveCompletionPresentationModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FdPullbackComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FinitePullbackStrictTowerComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FinitePullbackStrictTowerData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FinitePullbackTransitionGenerators` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteReductionAdditiveCompatibility` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteReductionScalarNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteReductionTowerResolvingModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FrameworkPbcPullbackComparisonData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralAmbientOperationModels` | S7 | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralCompletedTowerPullbackUniverses` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralDerivedPullbackLinear` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralObjectFiniteBasis` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralObjectPullbackQuotientBasis` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralOperationRoosEffectivity` | W2 | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralOperationsPreserveConstructible` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | N1 | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralOperationsWellDefined` | S4 | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralPrincipalConeQuotientAugmentation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralPullbackCompletedComparisonData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralPullbackCounitProjection` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralPullbackShiftCoordinates` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralPullbackSignedShift` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionTowerCanonical` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionTowerUnrestricted` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionTowerWellDefined` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionTransitionCocycles` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionTransitionSemilinear` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralStrictReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralTensorReductionTowerComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralTensorTransitionCompatibility` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IsomorphismComparisonNatural` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IsomorphismReductionTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IsomorphismScalarTensorKFlatModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedCompletionRealization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRAdicConeModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVREffectivity` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRKFlatReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRKFlatTransition` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedIntegralTensorTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedPullbackCompositionTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.OpenCompletedRestrictionIdentification` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.OrdinaryIntegralPullbackConstruction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.OrdinaryQuotientPullbackTowerComparison` | A3 | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointBalancedQuotientTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointEvaluationCompletionNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointFibreDerivedTensorModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointPullbackRepresentativeDiagram` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PrimitiveQuotientRealizationComparisons` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PullbackCommonStrictTowerModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurReductionLimitShiftAdjunction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurReductionLimitShiftData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceAdjointResolutionData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceAdjointResolutionShifts` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceKFlatComparisonData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceKFlatComparisonShifts` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceProjectionHomNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceReductionShifts` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceReductionUniversal` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.QcqsCompletionOrdinaryModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.RamifiedPullbackTowerData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.RoosAdjunctionQuotientNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ScalarPullbackStrictConeNaturality` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfStrictDirectImageScalarData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.StrictDvrFlatTensorSequence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.CompleteLiftedTopCellTriangle` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.CompletedTensorFiniteShift` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.CompletedTensorShiftRight` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent` | V2 | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.IsomorphismRoosUnitCancellation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.StrictQuotientCompletionUnit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.StrictQuotientConeAugmentation` | unclaimed | definitionally identical data; no adaptation |

## Status

landed 20261026T102415-L-355579 2026-10-26 (merge of deliver/W2/Sheaf.Paper.IntegralOperationRoosEffectivity)
