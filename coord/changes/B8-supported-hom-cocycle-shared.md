# AlgebraicGeometry.SupportedHomChiCocycle

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
attribute remains unchanged. The assigned `SupportedHomPullback` module publicly
imports the new module-valued transport interface, which reexports the normalization
interface. This normalization module keeps all its existing imports unchanged. No
theorem is weakened and no hole is added. The normalization dependency is unclaimed. No adopted source-library
construction, public import or attribute is changed.

Targets using these definitions need the usual renewed statement review. The
construction, normalization and target meanings are preserved by definitional equality.

## Old

```lean
def SupportedHomChiCocycle
    (theta : SupportedHomEvaluationIso J A j B)
    (chi : SupportedHomChi J A j B) : Prop :=
  ∀ (K I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
      [∀ r : ℤ, Injective (I.obj.X r)] (e : K ⟶ I) [QuasiIso e.hom] (a : ℤ)
      (x : ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj I.obj).cycles a),
    ∃! f : B ⟶ I.obj.X a,
      theta.hom.app (I.obj.X a) f =
        ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
          (ComplexShape.up ℤ) |>.obj I.obj).iCycles a x ∧
      ∃ hf : f ≫ I.obj.d a (a + 1) = 0,
        chi (DerivedCategory.Plus.Q.obj K) a
          ((Sheaf.supportSequenceModelIso J (ModuleCat.{u + 1} A)
            (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) I
            (DerivedCategory.Plus.Q.obj K) (supportedHomResolutionIso J A K I e).symm a).hom
              (((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj I.obj).homologyπ a x)) =
          ShiftedHom.map (Cocycle.equivHomShift.symm
            (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
            ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧' ≫
            (DerivedCategory.Plus.ι.map (supportedHomResolutionIso J A K I e).inv)⟦a⟧'
```

## New

```lean
def SupportedHomChiCocycle
    (theta : SupportedHomEvaluationIso J A j B)
    (chi : SupportedHomChi J A j B) : Prop :=
  ∀ (K I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
      [∀ r : ℤ, Injective (I.obj.X r)] (e : K ⟶ I) [QuasiIso e.hom] (a : ℤ)
      (x : ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj I.obj).cycles a),
    ∃! f : B ⟶ I.obj.X a,
      theta.hom.app (I.obj.X a) f =
        ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
          (ComplexShape.up ℤ) |>.obj I.obj).iCycles a x ∧
      ∃ hf : f ≫ I.obj.d a (a + 1) = 0,
        chi (DerivedCategory.Plus.Q.obj K) a
          ((Sheaf.supportSequenceModelIso J (ModuleCat.{u + 1} A)
            (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) I
            (DerivedCategory.Plus.Q.obj K) (supportedHomResolutionIso J A K I e).symm a).hom
              (((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj I.obj).homologyπ a x)) =
          supportedHomLocalizedCocycle I.obj a f hf ≫
            ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧' ≫
            (DerivedCategory.Plus.ι.map (supportedHomResolutionIso J A K I e).inv)⟦a⟧'
```

## Users

The listed downstream statements keep their meaning. Literal declaration uses are
internal to the assigned module or normalization interface; the new transport module
is the new consumer. No existing downstream proof needs an adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SupportedHomCocycleNormalization` | unclaimed | Definitionally equal cocycle formula with a proved construction equation. |
| `Sheaf.CategoryTheory.Abelian.ModuleSupportedHomTransport` | B8, new | Uses the shared cocycle in its normalization argument; no statement changes. |
| `Sheaf.Paper.SupportedHomPullback` | B8 | Uses the same named cocycle in Identification and coefficient transport. |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AffineSpaceZeroSectionPurity` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.ProjectionPurityAgreement` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.CartierClassAgreement` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.LineZeroClassEtaleRealization` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.PurityExteriorProductFrame` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.VectorBundleDiagonalOrientation` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.VectorBundleThom` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.VectorBundleThomMaps` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.VectorBundleThomProduct` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |

## Status

landed 20261022T025316-L-1272250 2026-10-22 (merge of deliver/B8/Sheaf.Paper.SupportedHomPullback)
