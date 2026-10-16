# Projection naturality and cached pro-etale tensor instances

## Reason

The naturality proof repeatedly elaborates the unbounded derived tensor and the
K-flat left-derived-functor side conditions. Reconstructing these instances at
each occurrence exceeded the single-file heartbeat/time budget. Cache the same
instances once in the unclaimed Derived.Tensor module. The added instances are
constructed from existing instances; they add no hypothesis, mathematical data
choice, sorry, or axiom. The monoidal-category aliases are definitionally equal
to the existing Mod.derivedMonoidalCategory and its underlying structure.

The assigned module also keeps Functor.rightDerivedFunctor and
Functor.mapDerivedCategory irreducible locally while comparing the bounded
subcategory maps with the unbounded maps. Explicitly reducing just the lifts
then proves naturality without reducing localization implementations. This
attribute is local. Existing public declaration signatures and public imports
are unchanged in both files. No target changes meaning, so target-statement
review is not reopened. No module held by another group is adapted.

## Old

There were no direct instances for the three graded tensor conditions or for
the two derived monoidal structures specialized to these module categories.
Generic instance synthesis reconstructed the instances at each use.

There was no local transparency directive in ProjectionFormula. Its original
bounded naturality proofs were `sorry`.

## New

Derived.Tensor adds exactly the following proved shortcut instances:

```lean
/-- A direct instance of the derived monoidal category on module objects. -/
noncomputable instance monoidalCategory_derivedModule (Z : Scheme.{u}) :
    MonoidalCategory
      (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :=
  Mod.derivedMonoidalCategory

/-- Cache the underlying tensor data without reconstructing the derived coherence proofs. -/
noncomputable instance monoidalCategoryStruct_derivedModule (Z : Scheme.{u}) :
    MonoidalCategoryStruct
      (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :=
  (monoidalCategory_derivedModule Λ Z).toMonoidalCategoryStruct

/-- Cached fourfold tensor existence for graded module objects. -/
instance hasTensor4_gradedModule (Z : Scheme.{u})
    (A B C D : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    GradedObject.HasTensor₄ObjExt A B C D := inferInstance

/-- Cached compatibility for the first parenthesization of a graded triple tensor. -/
instance hasGoodTensor12_gradedModule (Z : Scheme.{u})
    (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := inferInstance

/-- Cached compatibility for the second parenthesization of a graded triple tensor. -/
instance hasGoodTensor23_gradedModule (Z : Scheme.{u})
    (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := inferInstance

```

ProjectionFormula adds private formal naturality lemmas and proves its three
naturality obligations. It also proves the open-immersion derived projection
formula by linearized full faithfulness, the relative tensor coequalizer, and
a K-flat complex representative. Its additional import of
WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
is proof-only. All added helpers are private and proved. Its bounded section uses:

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
```

All original theorem signatures and definition bodies are textually unchanged.
All original public imports remain. The new aliases select definitionally the
same tensor data, and the graded side conditions are propositions.

## Users

The read-only downstream.py query lists the transitive importers below.
The declaration-use query for the added names has no existing users: importers
can use the new instances through inference. None needs a source adaptation;
all statements, definitions, and their mathematical meanings are preserved.
The two files edited here are named explicitly. Other sandbox source files are
byte-identical copies of the shared source, used to compile against its current
interfaces while the published build still exposed older ones.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | four proofs and local elaboration control |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor | unclaimed | proved instance shortcuts only |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CoefficientExchangeFromComparisons | B2 | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarPullbackCube | E1 | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | E4 | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | F1 | same tensor data and signatures; no adaptation |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | B3 | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | F2 | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | same tensor data and signatures; no adaptation |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | same tensor data and signatures; no adaptation |
| TargetsCheck | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | A4 | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal | D4 | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | G2 | same tensor data and signatures; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.SmoothPurity.Defs | G1 | same tensor data and signatures; no adaptation |
| WeilConjectures.TateTwist.ProEtale | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.TraceFormula.Basic | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.TraceFormula.Main | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.TraceFormula.Stalk | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | same tensor data and signatures; no adaptation |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | same tensor data and signatures; no adaptation |

## Status

landed 20261016T221611-L-1615633 2026-10-16 (merge of deliver/H1/WeilConjectures.PoincareDuality.ProjectionFormula)
