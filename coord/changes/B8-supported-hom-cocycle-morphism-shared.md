# AlgebraicGeometry.SupportHomPair.cocycleMorphism

## Reason

The full single-complex cocycle construction was repeatedly unfolded while Lean checked
normalization and coefficient-transport proofs. Give that existing map the shared,
irreducible definition `AlgebraicGeometry.supportedHomLocalizedCocycle` in the
normalization interface, together with its proved equation
`AlgebraicGeometry.supportedHomLocalizedCocycle_eq`. Both definitions in this repair
now use that map. No argument is moved out of the assigned proof: its normalization,
coefficient-change, exchange and coherence arguments remain there.

The new map is exactly the old `ShiftedHom.map` expression. Unfolding its definition
proves the old/new body equation by reflexivity. Every existing signature and
attribute remains unchanged, and the shared module-valued transport interface is publicly imported. Its public
imports expose the cocycle and derived Hom-map constructions needed by the assigned
public definitions. No theorem is weakened and no hole is
added. The normalization dependency is unclaimed. No adopted source-library
construction, public import or attribute is changed.

Targets using these definitions need the usual renewed statement review. The
construction, normalization and target meanings are preserved by definitional equality.

## Old

```lean
def cocycleMorphism
    (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ)
    (f : S.supported ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0) :
    (DerivedCategory.singleFunctor (Sheaf S.topology (ModuleCat.{u + 1} A)) 0).obj
      S.supported ⟶ (DerivedCategory.Plus.Q.obj I).obj⟦a⟧ :=
  ShiftedHom.map (Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
    ((DerivedCategory.quotientCompQhIso _).hom.app I.obj)⟦a⟧'
```

## New

```lean
def cocycleMorphism
    (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ)
    (f : S.supported ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0) :
    (DerivedCategory.singleFunctor (Sheaf S.topology (ModuleCat.{u + 1} A)) 0).obj
      S.supported ⟶ (DerivedCategory.Plus.Q.obj I).obj⟦a⟧ :=
  supportedHomLocalizedCocycle I.obj a f hf ≫
    ((DerivedCategory.quotientCompQhIso _).hom.app I.obj)⟦a⟧'
```

## Users

The listed downstream statements keep their meaning. Literal declaration uses are
internal to the assigned module or normalization interface; the new transport module
is the new consumer. No existing downstream proof needs an adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SupportedHomPullback` | B8 | Uses the shared cocycle and its original quotient comparison. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.CartierClassAgreement` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.LineZeroClassEtaleRealization` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityExteriorProductFrame` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleDiagonalOrientation` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThom` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThomMaps` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThomProduct` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AffineSpaceZeroSectionPurity` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.ProjectionPurityAgreement` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |

## Status

landed 20261022T025316-L-1272250 2026-10-22 (merge of deliver/B8/Sheaf.Paper.SupportedHomPullback)
