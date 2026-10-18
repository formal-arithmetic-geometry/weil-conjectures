# CondensedFieldContinuousRealization public imports

## Reason

The existing public import of `MorphismDefs` makes the constructible Serre API import the
bounded-constructible restricted-functor module back through the base-change definitions.
This prevents using its proved Serre theorems to prove tensor preservation. The realization
module needs the basic module-object pullback API, and its consumers also need
`CondensedRing.upperStar`, `upperStarComp`, the finite-presentation/free-module API,
and the localization restriction adjunction/comparison API.
Replacing this import by `UpperLowerStar.Defs`, `ConstructibleSheaf.ProEtaleModule.Def`,
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`,
and `ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
retains those exports and removes that cycle. The module is unclaimed. No declaration signature, definition, proof,
visibility attribute or target statement changes.

Repair of return at head `75269cf1e`: the import-pruning check additionally found
`constructible_of_iso` from `Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`
used in four consumers. The realization module retains that public export with a direct
public import of the defining pullback module, preserving the consumer API without the
base-change cycle. Each listed consumer also imports that defining module directly and privately.
Two consumers are new modules of this delivery; the existing Paper modules are unclaimed
and receive only the additional import. Their signatures, visibility and proofs are unchanged.

Repair of return at head `182ee533b`: two more unclaimed consumers require direct imports.
`Sheaf.Paper.ContinuousModuleEncodingScalarExtension` receives the private import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`;
`Sheaf.PoincareDuality.CompatiblePrimitiveRoots` receives the public import
`WeilConjectures.AlgebraicGeometry.Sites.Kummer`, which supplies its public root-system
definition. The roots adaptation adds Kummer publicly and also imports
`WeilConjectures.Mathlib.AlgebraicGeometry.Limits` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Restrict` privately. The latter two provide
`Scheme.isEmpty_of_subsingleton_Γ` and `Scheme.isUnit_ι_appTop_basicOpen`, whose absence
was detected when compiling its unchanged proof bodies against the reduced dependency
closure. No other line in the roots module changes. The
scalar-extension module additionally renames its private helper `tensorHomEquiv` to
`scalarExtensionTensorHomEquiv` and updates its one use. The required import brings the
public `SheafOfModules.tensorHomEquiv` into scope, and Lean otherwise reports
"a non-private declaration `SheafOfModules.tensorHomEquiv` has already been declared".
The helper type/body and all public signatures and visibility attributes are unchanged.

## Old

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
```

The scalar-extension private helper was originally declared as:

```lean
private noncomputable def tensorHomEquiv
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    (changeOfRings α M ⟶ N) ≃
      (M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :=
```

## New

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
```

The scalar-extension helper retains the same type and body under its fresh private name:

```lean
private noncomputable def scalarExtensionTensorHomEquiv
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    (changeOfRings α M ⟶ N) ≃
      (M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :=
```

Its only caller uses `let e := scalarExtensionTensorHomEquiv α`.

## Users

The table lists every transitive consumer from `tools/downstream.py`, plus the adapted module.
The previous unchanged-consumer check did not satisfy the source import-pruning gate;
this repair addresses every consumer named in the return explicitly. Compilation now
checks all fifteen delivery modules together in import order against the published library.
The two existing adapted modules are copied from the current shared source and differ
only by the import below. No target statement or definition changes meaning.
The previous repair passed its source import-pruning check and dry run, but landing on
the newer base exposed the two additional consumers repaired in this retry. This retry
checks all fifteen delivery modules together.

For each of `Sheaf.AlgebraicGeometry.BoundedConstructibleHomPreservation`,
`Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated`,
`Sheaf.Paper.ConstructibleCokernelsExtensions`, and `Sheaf.Paper.IntegralConstructibleKernels`,
the additional proof-only import is:

```lean
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
```

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BoundedConstructibleHomPreservation | B2 (new helper) | Direct private import supplies the constructibility API after removal of MorphismDefs. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated | B2 (new helper) | Direct private import supplies the constructibility API after removal of MorphismDefs. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Replaced an unused public import; all declarations and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Original source compiled unchanged against the reduced public imports. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | Original source compiled unchanged against the reduced public imports. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Original source compiled unchanged against the reduced public imports. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Original source compiled unchanged against the reduced public imports. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Original source compiled unchanged against the reduced public imports. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | Original source compiled unchanged against the reduced public imports. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Added only the direct private import requested by the return; signatures, visibility and proofs unchanged. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Original source compiled unchanged against the reduced public imports. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Added the direct private MonoidalClosed import; renamed the colliding private tensorHomEquiv helper and its use. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Added only the direct private import requested by the return; signatures, visibility and proofs unchanged. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Original source compiled unchanged against the reduced public imports. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| TargetsCheck | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.PoincareDuality.Poincare | A4 | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No declaration, definition or target meaning changes; transitive import provenance only. |

| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | unclaimed | Added public Kummer and private Limits/Restrict imports required by the unchanged root-system definition and proofs. |

| Sheaf.PoincareDuality.CompatibleIntegralRootBases | unclaimed | Public declarations and mathematical meaning unchanged; direct consumer dependencies checked by the import-pruning gate. |
| Sheaf.PoincareDuality.IntegralResidueLimit | unclaimed | Public declarations and mathematical meaning unchanged; direct consumer dependencies checked by the import-pruning gate. |
| Sheaf.PoincareDuality.IntegralResidueQuotient | unclaimed | Public declarations and mathematical meaning unchanged; direct consumer dependencies checked by the import-pruning gate. |
| Sheaf.PoincareDuality.IntegralTateBasis | unclaimed | Public declarations and mathematical meaning unchanged; direct consumer dependencies checked by the import-pruning gate. |
| Sheaf.PoincareDuality.IntegralTateLocalLine | unclaimed | Public declarations and mathematical meaning unchanged; direct consumer dependencies checked by the import-pruning gate. |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | unclaimed | Public declarations and mathematical meaning unchanged; direct consumer dependencies checked by the import-pruning gate. |

## Status

landed 20261018T103528-L-17731 2026-10-18 (merge of deliver/B2/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible)
