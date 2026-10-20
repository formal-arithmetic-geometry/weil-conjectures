# WeilConjectures.integralScalarTransition_existsUnique

## Reason

Fill the existing transition existence-and-uniqueness proof. This is not a statement
or public definition repair. The old and new statements are identical; all 26
existing public declaration signatures and all public imports remain identical.

The first dry run requested a change record because its conservative static
classification flags new commands (`namespace`, `universe`, `variable`, local
`attribute`, and a section-scoped elaboration option). This record makes that
classification reviewable. The new generic variables are inside
`SheafOfModules.IntegralScalarProof`, which is closed before the original namespace.
All added declarations there are private. The coefficient-specific helpers and
local attributes are inside `section ScalarTransitions`, closed immediately after
the proved theorem. No new global instance or notation is introduced. The added
`import all Sheaf.Paper.IntegralReductionTowerUnrestricted` is private and only
allows this proof to reuse that module's proved private tensor-map implementation.

No consumer needs a forced adaptation. In particular,
`Sheaf.Paper.IntegralScalarExtension` continues to select the functor from the
unchanged main theorem `integralScalarExtensionWellDefined`; that theorem and its
statement are untouched. The actual tensor transition now has a complete proof
of the same uniqueness property used by its existing definition.

## Old

```lean
theorem integralScalarTransition_existsUnique (n : ℕ) :
    ∃! τ : integralScalarLevel l E L ι Y (n + 1) ⟶ integralScalarLevel l E L ι Y n,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (U : Y.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj U)
        (x : (P.X i).val.obj U),
        ((τ.app P).f i).val.app U
          (integralScalarTensorSection l E L ι Y (n + 1) (P.X i) U s x) =
        integralScalarTensorSection l E L ι Y n (P.X i) U
          ((integralCoefficientSheafTransition l L Y n).hom.app U s) x := by
  sorry
```

## New

```lean
theorem integralScalarTransition_existsUnique (n : ℕ) :
    ∃! τ : integralScalarLevel l E L ι Y (n + 1) ⟶ integralScalarLevel l E L ι Y n,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (U : Y.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj U)
        (x : (P.X i).val.obj U),
        ((τ.app P).f i).val.app U
          (integralScalarTensorSection l E L ι Y (n + 1) (P.X i) U s x) =
        integralScalarTensorSection l E L ι Y n (P.X i) U
          ((integralCoefficientSheafTransition l L Y n).hom.app U s) x := by
  let τ : integralScalarLevel l E L ι Y (n + 1) ⟶ integralScalarLevel l E L ι Y n :=
    { app := fun P ↦
        { f := fun i ↦ integralScalarModuleStep l E L ι Y n (P.X i)
          comm' := fun i j _ ↦ (integralScalarModuleStep_naturality l E L ι Y n
            (P.d i j)).symm }
      naturality := fun P Q a ↦ by
        apply HomologicalComplex.hom_ext
        intro i
        exact integralScalarModuleStep_naturality l E L ι Y n (a.f i) }
  refine ⟨τ, (fun P i U s x ↦ integralScalarModuleStep_tmul l E L ι Y n (P.X i) U s x), ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  apply integralScalarReduction_hom_ext l E L ι Y (n + 1) (P.X i)
  intro U s x
  exact (hτ' P i U s x).trans (integralScalarModuleStep_tmul l E L ι Y n (P.X i) U s x).symm
```

The private constructions implementing this proof are in the same delivered Lean
file. They introduce no new proof obligation. The axiom check for the displayed
theorem is exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Users

`tools/downstream.py Sheaf.Paper.IntegralScalarExtensionWellDefined --uses
integralScalarTransition_existsUnique` reports only this module as a textual user
of that declaration. The table additionally lists the complete transitive import
closure (154 modules at this check), so every potentially affected importer is
explicit. Holders are from the current claim records. None is edited.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | W5 | Transition theorem proved; signatures unchanged. |
| `Sheaf.Algebra.Homology.RingedSiteTorFlatModel` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Algebra.Homology.SitePerfectLowerModel` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Algebra.Homology.SitePerfectTorWindow` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Algebra.Homology.SitePerfectUpperModel` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.GeometricSpecializationCategory` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.MultipointedCurveModification` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SemistableMultipointedPair` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictlySemistableCurve` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization` | unclaimed | No interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness` | unclaimed | No interface change; no adaptation. |
| `Sheaf.CategoryTheory.SiteTorIntervalRestriction` | unclaimed | No interface change; no adaptation. |
| `Sheaf.CategoryTheory.Sites.CoherentConservativeReflection` | unclaimed | No interface change; no adaptation. |
| `Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient` | unclaimed | No interface change; no adaptation. |
| `Sheaf.CategoryTheory.Sites.CoherentObjectApproximation` | unclaimed | No interface change; no adaptation. |
| `Sheaf.CategoryTheory.Sites.CoherentToposRepair` | unclaimed | No interface change; no adaptation. |
| `Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent` | unclaimed | No interface change; no adaptation. |
| `Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent` | unclaimed | No interface change; no adaptation. |
| `Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.AlgebraicallyClosedCoefficients` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.AlterationBlowupFinite` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.AlterationFiniteRefinement` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | Z9 | No interface change; no adaptation. |
| `Sheaf.Paper.CoefficientTwistsDetailed` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.CoherentSetCriterion` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.CompleteResidueCohomologyBounds` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.CompletedScalarShift` | F3 | No interface change; no adaptation. |
| `Sheaf.Paper.ConstantCoefficientObjectsConstructible` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.ConstructibleFlatCohomologyTorBound` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.ConstructibleHeart` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.ConstructibleStandardTStructure` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.DerivedCompleteOnSlices` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.DerivedCompleteUnrestricted` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.EtaleIntegralLineDerivedComplete` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.ExceptionalAdjointAdmissibility` | V7 | No interface change; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | V8 | No interface change; no adaptation. |
| `Sheaf.Paper.FiniteStagePairCategory` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.GeneralNearbySliceTest` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.GoodOrientedNearbyKunneth` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.HomUniversalCoefficients` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleLinear` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.IntegralHomReduction` | M4 | No interface change; no adaptation. |
| `Sheaf.Paper.IntegralLineTensorComparison` | H7 | No interface change; no adaptation. |
| `Sheaf.Paper.IntegralLineTensorCompleteness` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.IntegralOperationsPreserveConstructible` | T5 | No interface change; no adaptation. |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.IntegralOperationsScalarExtension` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.IntegralScalarExtension` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.IntegralScalarExtensionConstructible` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.IntegralScalarExtensionUniverses` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.ModificationClosedImageLifting` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.ModificationsZariskiRefinement` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.NearbyClosedImage` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.NearbyCyclesDimensionBound` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.NearbyFiniteBaseDescent` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.NearbyGeometricSlice` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.NearbyProperHyperdescent` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.NearbySpecializationSlice` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.NearbySpreadOut` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.NormalizedDVREffectivity` | T6 | No interface change; no adaptation. |
| `Sheaf.Paper.OrgogozoInductionData` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedClosedBaseExtension` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedClosedBaseRestriction` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleCoherent` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleSetSheaf` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleSheaf` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleSheafVanishing` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleSubquotients` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedHypercoverDescentDatum` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedMaximalPointFiniteness` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedNearbyCycles` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedNearbyStrictLocalDescription` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedProductPointsConservative` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedProperFibreExchange` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.OrientedSourceLocalization` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PbcAutomorphismTransport` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PbcFilteredRetractDescent` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PbcFiniteCompletedCoefficientMap` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PbcWeilCategory` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PointDerivedHomEvaluation` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PointReductionUnitNormalization` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PointReductionUnits` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PointSectionsDerivedReduction` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PointSectionsFiniteReduction` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PointSectionsFiniteness` | P3 | No interface change; no adaptation. |
| `Sheaf.Paper.PointSectionsScalarExtension` | G2 | No interface change; no adaptation. |
| `Sheaf.Paper.PointSectionsTensorShift` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PsiConstructibilityDescent` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.PurTwistSheafLocallyFree` | W9 | No interface change; no adaptation. |
| `Sheaf.Paper.RationalSliceCompletedEvaluation` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.RationalThickEvaluation` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.RationalizationIdempotentComplete` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.RationalizationKaroubi` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.ScalarExtensionComposition` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.ScalarExtensionExact` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.SfIntegralDirectImageConstructible` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.SfRationalLocalGlobalPowerTorsion` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.SignedLineTensorEquivalence` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.StratifiedOrientedCover` | unclaimed | No interface change; no adaptation. |
| `Sheaf.Paper.WeilTensorProduct` | J4 | No interface change; no adaptation. |
| `Sheaf.SixFunctors.TraceFormula.NodalEtaleChart` | unclaimed | No interface change; no adaptation. |
| `Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel` | unclaimed | No interface change; no adaptation. |
| `Sheaf.SixFunctors.TraceFormula.NodalLogRegularity` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ClosedImageGenericAlteration` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ContractedComponentGenericData` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ContractedComponentNoExtraGeneric` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.CurveP1TreeLocalCriterion` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.FinitarySiteCoherentGenerators` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.FiniteCoverTubeComparison` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.FiniteEtaModificationGluing` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.FiniteFibreValuationDomination` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.GabberNearbyCycleDimensionBound` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.LocalMarkingLength` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.MarkedCurveFiniteTypeModel` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.NodalContractionNormalizationBranches` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.OrientedPointCohomology` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.OrientedPointNormalizedStratum` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ProjectiveLineTree` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ProperBaseChangeCoherentConservative` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ReducedFibreModification` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.SemistableMarkedPoint` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.SemistableModificationFibreContractions` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.SemistableNormalTargetFactorization` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.SingleValuationSemistableExtraction` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.StableModificationStabilityFieldDescent` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ValuationCurveProjectivePreparation` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ValuationExceptionalLocalCriterion` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ValuationHorizontalCurveModels` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ValuationModificationProperCompletion` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ValuationNormalizedGraphModel` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ValuationReducedFibreNormalization` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ValuationStrictSemistableCofinality` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization` | unclaimed | No interface change; no adaptation. |
| `Sheaf.TraceFormula.ValuationSymmetricNodalBlowup` | unclaimed | No interface change; no adaptation. |

## Status

landed 20261020T211850-L-3511843 2026-10-20 (merge of deliver/W5/Sheaf.Paper.IntegralScalarExtensionWellDefined)
