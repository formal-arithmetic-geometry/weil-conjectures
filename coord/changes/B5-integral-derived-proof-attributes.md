# WeilConjectures.IntegralOnSlice.completedTensor_global_comparison

## Reason

Stage-3 preflight conservatively classified the added local reducibility declaration
as a command changing what importers see and requested a change record. The declaration
is local to proof elaboration in this module. It keeps the completed ring, chosen duality
model and tensor construction abstract while Lean checks the comparisons.

All existing public signatures, public definition bodies, public imports and effective
exported attributes are preserved. No target statement changes meaning and no definition
repair or consumer adaptation is made. `completion_exists` and the global tensor comparison
are now proved, with private proof helpers and private proof imports.

## Old

There was no local reducibility declaration at this position. The original theorem was:

```lean
theorem completedTensor_global_comparison :
    Nonempty (((integralOperationsGoodLocalization l E X).prod
      (integralOperationsGoodLocalization l E X)) ⋙ completedTensor l E X none ≅
        integralOperationsTensorOnGood l E X) := by
  sorry
```

## New

The added command and the unchanged theorem signature with its complete proof are:

```lean
attribute [local irreducible] duality SheafOfModules.monoidalCategory
  HasDerivedCategory.standard constantSheaf
  completedIntegralCoefficientSheafUnrestricted

theorem completedTensor_global_comparison :
    Nonempty (((integralOperationsGoodLocalization l E X).prod
      (integralOperationsGoodLocalization l E X)) ⋙ completedTensor l E X none ≅
        integralOperationsTensorOnGood l E X) := by
  obtain ⟨a⟩ := tensorCompletionOnGood l E X
  obtain ⟨b⟩ := integralTensorReductionTowerComparison l E X
  let H := (integralOperationsGoodComplex l E X).ι.prod
    (integralOperationsGoodComplex l E X).ι
  let T := coefficientTotalTensor.{u, t + 1, t} (topology X none) (ring l E X none)
  let R := integralOperationsRoosFunctor (A := Mod l E X none)
  let Q := DerivedCategory.Q (C := Mod l E X none)
  let W := tower l E X none
  let V := integralOperationsTensorTowerFunctor l E X
  have e : totalTensorOnGood l E X ⋙ (Good l E X none).ι ≅ H ⋙ T :=
    (Good l E X none).liftCompιIso (H ⋙ T) (fun P ↦ totalTensorGood l E X P.1 P.2)
  have b' : T ⋙ W ≅ V := by
    dsimp only [T, W, V]
    rw [globalTower_eq]
    exact b
  refine ⟨a ≪≫ ?_⟩
  exact (Functor.associator (totalTensorOnGood l E X)
      (Good l E X none).ι (roos l E X none ⋙ Q)).symm ≪≫
    Functor.isoWhiskerRight e (roos l E X none ⋙ Q) ≪≫
    Functor.isoWhiskerLeft (H ⋙ T) (Functor.associator W R Q) ≪≫
    (Functor.associator (H ⋙ T) W (R ⋙ Q)).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator H T W) (R ⋙ Q) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft H b') (R ⋙ Q) ≪≫
    Functor.associator H V (R ⋙ Q) ≪≫
    Functor.isoWhiskerLeft H (Functor.associator V R Q).symm
```

## Users

The table includes all 45 downstream modules reported by `tools/downstream.py` and the
item itself. The named theorem has no use outside the item in that source scan.
Claims are the available current claim records; none of these consumers is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralDerivedOperationsOnSlices | B5 | Proofs filled; local proof attributes added. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.CompletedScalarChainShift | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.CompletedScalarShift | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.DerivedCompleteOnSlices | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.EtaleIntegralLineDerivedComplete | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | V8 | Public interface preserved; no adaptation. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.IntegralLineTensorComparison | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.IntegralLineTensorComparisonDefinitions | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.IntegralLineTensorComparisonIso | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.IntegralLineTensorComparisonRepresentative | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.IntegralLineTensorCompleteness | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | K2 | Public interface preserved; no adaptation. |
| Sheaf.Paper.IntegralStratifiedPerfectClosureHomology | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.PointSectionsScalarExtension | G3 | Public interface preserved; no adaptation. |
| Sheaf.Paper.PointSectionsTensorShift | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.SfIntegralStandardTruncations | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | unclaimed | Public interface preserved; no adaptation. |
| Sheaf.Paper.StratifiedPerfectInternalHomCoproducts | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Public interface preserved; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Public interface preserved; no adaptation. |

## Status

landed 20261021T020959-L-2686655 2026-10-21 (merge of deliver/B5/Sheaf.Paper.IntegralDerivedOperationsOnSlices)
