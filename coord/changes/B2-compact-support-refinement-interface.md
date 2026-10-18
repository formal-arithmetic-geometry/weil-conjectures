# AlgebraicGeometry.Etale.compactSupportProperOpenRefinementMap

## Reason

Kernel checking repeatedly exceeded the 60-second limit while converting the stored
formalism compositor to the concrete derived direct-image compositor. Construct the map
with the latter directly, using the same alpha and exactly the same canonical compositor.
The existing proved theorem `derivedPlusFormalism_pfComp'_inv` identifies the old compositor
with `Functor.rightDerivedFunctorPlusCompIso'` of `lowerStarComp`, including its injective
preservation instance. Thus the old and new expressions are equal: apply that theorem at
`r.hom`, `d.g`, `c.g`, `r.hom_g`, evaluate at `D(c.i)_! K`, and postcompose the unchanged
`R(d.g)_*(alpha_r)`. This is a canonical-construction repair, not a change of map.

The definition's signature is unchanged. No target theorem signature changes. A target using
this definition requires semantic re-review under AGENTS.md section 4; the compositor
normalization above proves preservation of its intended meaning. No data is chosen from
an undetermined existence statement. A separate consumer check of the complete original
formula compiled in 6.5 seconds, with proof `rw [derivedPlusFormalism_pfComp'_inv ...]; rfl`.
The full item compiled in 9.3 seconds after the repair.

## Old

```lean
noncomputable def compactSupportProperOpenRefinementMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) d).obj K ⟶
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K :=
  (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) d.g).map
      (properOpenComparison Λ r.hom c.i d.i r.i_hom K) ≫
    ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).pfComp'
      r.hom d.g c.g r.hom_g).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj K)

```

## New

```lean
noncomputable def compactSupportProperOpenRefinementMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) d).obj K ⟶
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K :=
  letI : (lowerStar (ModuleCat.{u + 1} Λ) r.hom).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom)
  (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) d.g).map
      (properOpenComparison Λ r.hom c.i d.i r.i_hom K) ≫
    (Functor.rightDerivedFunctorPlusCompIso'
      (lowerStar (ModuleCat.{u + 1} Λ) r.hom) (lowerStar (ModuleCat.{u + 1} Λ) d.g)
      (lowerStarComp (ModuleCat.{u + 1} Λ) r.hom d.g c.g r.hom_g.symm)).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj K)

```

The following local attribute is used in the private proof helpers. It exports no
reducibility change or instance to consumers.

```lean
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryPlus
  CategoryTheory.Functor.rightDerivedFunctorPlus lowerStar upperStar
  properOpenComparison properOpenIdentification
  CategoryTheory.Functor.rightDerivedFunctorPlusCompIso' properOpenDirectImageCompIso
```

The composition helper locally respects transparency for terms and types:

```lean
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
```

The Cartesian helper locally uses the project's existing permissive settings:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

Every added helper is private and proved. The only new public declaration is the separately
recorded normalization lemma in its new module and DAG node.


## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion --uses
compactSupportProperOpenRefinementMap` reports 389 downstream importing modules, and one
module using the declaration name: the item itself. Its theorem signature is unchanged.
All other importers have no occurrence of this declaration name, and the construction
continues to denote the same map by the existing compositor normalization theorem.
No consumer adaptation is required. The comparison-composition module is held by F2 and
is used unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | M3 | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons | C4 | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | C6 | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | X2 | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | H3 | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | X3 | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | B4 | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | S1 | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.PoincareDuality.CompatibleIntegralRootBases | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.PoincareDuality.IntegralResidueLimit | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.PoincareDuality.IntegralResidueQuotient | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.PoincareDuality.IntegralTateBasis | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.PoincareDuality.IntegralTateLocalLine | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| TargetsCheck | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | B3 | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | B2 | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.Statement | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same canonical map; no direct occurrence or adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion | B2 | B2 adapts the construction and proofs; all existing public signatures remain identical. |

## Status

landed 20261018T091358-L-3253393 2026-10-18 (merge of deliver/B2/Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion)
