# AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit

## Reason

The new proof uses local irreducibility annotations to keep elaboration from unfolding
inverse-image functors, cohomological pullback and Ext's transported additive-group instance.
They are confined to this file. No existing signature, definition, visibility or public
import changes, and no downstream module is adapted. The interface detector conservatively
flags these local attribute commands, so their scope is recorded here.

## Old

There was no local irreducibility command before the elementwise continuity theorem.
Its original signature, retained verbatim, is:

```lean
theorem cohomologyMap_isColimit_of_isLimit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ) :
    (∀ x : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F) q,
      ∃ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
        Etale.cohomologyMap (c.π.app i).left _ q y =
          Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app i).left (D.obj i).hom
            c.pt.hom (Over.w (c.π.app i)).symm).hom.app F) q x) ∧
    ∀ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
      Etale.cohomologyMap (c.π.app i).left _ q y = 0 →
        ∃ (j : I) (g : j ⟶ i), Etale.cohomologyMap (D.map g).left _ q y = 0
```

## New

```lean
attribute [local irreducible] upperStar cohomologyMap Sheaf.H.map
  CategoryTheory.Abelian.Ext.instAddCommGroup
```

The theorem also locally sets `backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` to true. These elaboration settings have no
exported effect. The theorem's hypotheses, universes and conclusion are identical.

## Users

Source-only inventory: `python3 tools/downstream.py
WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity --names`.
Every listed consumer sees the identical interface; no target meaning is changed.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity | W2 | Same exported declarations and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison | unclaimed | Same exported declarations and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | Same exported declarations and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison | unclaimed | Same exported declarations and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections | unclaimed | Same exported declarations and public imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel | unclaimed | Same exported declarations and public imports; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same exported declarations and public imports; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | C2 | Same exported declarations and public imports; no adaptation. |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | Same exported declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same exported declarations and public imports; no adaptation. |
| TargetsCheck | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.AffineBaseChange | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.BaseChange | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.ExtensionInvariance | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.FieldExtensionInjective | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Comparison | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Counterexample | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic | V2 | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.AlgClosedField | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Comparison | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ComparisonMonoidal | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Constructible | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Duality | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Finiteness | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.FlatModel | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekIndependence | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjectionComparison | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormulaExtendScalars | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ScalarExtension | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Shift | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Stability | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitudeResidue | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.WeilComplex | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusLift | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicRange | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineLine | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineReduction | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FiniteModel | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Iterate | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.KernelPushforward | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.LocalFrobenius | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ModelRestriction | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperCurve | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardFibres | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardStep | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceClass | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceMap | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same exported declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same exported declarations and public imports; no adaptation. |

## Status

landed 20261016T000944-L-3678012 2026-10-16 (merge of deliver/W2/WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity)
