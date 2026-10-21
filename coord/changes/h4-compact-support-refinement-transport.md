# AlgebraicGeometry.ProEtale.properTransportRefinementPlus

## Reason

Normalizing the inverse of the refinement composite exceeded the 60-second file limit.
The cause is equality transport at the level of entire derived functor structures:
`eqToIso (congrArg (fun q => (lowerStar _ q).rightDerivedFunctorPlus) h)`.
The source library already documents this performance issue in
`ProEtale.rightDerivedLowerShriekCongr`.

Use `properTransportDirectImageCongr`, defined by induction on equality of the scheme
maps, before evaluating the isomorphism at an object. Its proved `_eqToIso` theorem
identifies it with the original transport, and `_rfl` records its reflexive equation.
Thus every existing declaration signature and every mathematical map is preserved.
The inverse formula and bounded-below refinement square now compile in about 13 seconds
inside the item module. No source-library module is changed.

## Old

```lean
def properTransportRefinementPlus {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (eqToIso (congrArg
      (fun q ↦ (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctorPlus)
      r.hom_g.symm)).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)) ≪≫
    (proEtaleComparisonDirectImageCompIso A r.hom d.g).symm.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctorPlus.mapIso
      (properOpenProEtaleIsoPlus A r.hom c.i d.i r.i_hom L).symm
```

## New

```lean
/-- Transport proper direct image by equality of scheme maps, without comparing
large derived functor structures when the equality transport is evaluated.
Source: equality induction; the original refinement transport
(blueprint: def-sf-refinement-comparison-isomorphism). -/
def properTransportDirectImageCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus ≅
      (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlus := by
  subst g
  exact Iso.refl _

omit [Finite A] in
/-- Equality transport is the identity for a reflexive equality. -/
@[simp]
theorem properTransportDirectImageCongr_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    properTransportDirectImageCongr A (rfl : f = f) = Iso.refl _ := rfl

omit [Finite A] in
/-- This efficient equality transport is the usual transport isomorphism. -/
theorem properTransportDirectImageCongr_eqToIso {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) :
    properTransportDirectImageCongr A h = eqToIso (congrArg
      (fun t ↦ (lowerStar (ModuleCat.{u + 1} A) t).rightDerivedFunctorPlus) h) := by
  subst g
  rfl

/-- The actual refinement arrow on bounded-below comparison inputs: the direct-image
compositor followed by the proper image of the inverse specified proper/open arrow.
It is meaningful for every refinement, including noncartesian refinements.
Source: Stacks 0F7I, and def-sf-refinement-comparison-isomorphism, part (b)
(blueprint: def-sf-refinement-comparison-isomorphism). -/
def properTransportRefinementPlus {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (properTransportDirectImageCongr A r.hom_g.symm).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)) ≪≫
    (proEtaleComparisonDirectImageCompIso A r.hom d.g).symm.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctorPlus.mapIso
      (properOpenProEtaleIsoPlus A r.hom c.i d.i r.i_hom L).symm
```

## Users

`tools/downstream.py Sheaf.Paper.RefinementComparisonIsomorphism --uses
AlgebraicGeometry.ProEtale.properTransportRefinementPlus` lists 122 transitive importers.
Only the defining source module mentions the plus declaration. A separate textual check
of `properTransportRefinement` finds the item and
`Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport`; neither existing signature
changes. The original `ProperCompositionSiteTransport` was compiled against the repaired
dependency in 15.2 seconds without edits. Its statement only mentions the ambient map
and needs no adaptation.
No other module's statement becomes weaker, stronger, or different: the equality theorem
identifies the only replaced factor. The independent reader should check this equality
when reviewing target meanings through this definition.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.Paper.CanonicalOriginCompactSupportComposition` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.Paper.CompactSupportSiteCoherence` | H4 | Prove the coherence theorem using the repaired definition. |
| `Sheaf.Paper.CompactificationCoherence` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.Paper.CompositeIntegrationCounit` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.Paper.FiniteCompactSupportConstructibility` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.Paper.ProEtaleCompositionTowerNormalization` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.Paper.PurityFiniteExceptionalComposition` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.Paper.RefinementComparisonComposition` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.Paper.RefinementComparisonIsomorphism` | unclaimed | Definition repair; existing signatures preserved. |
| `Sheaf.Paper.StandingExceptionalComposition` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.Paper.TraceExceptionalAdmissibility` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | Same map by proved transport equality; no adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed | Same map by proved transport equality; no adaptation. |
| `TargetsCheck` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveTopCohomology` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierStalk` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.Karoubian` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.KaroubianPointer` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.LissePoincarePairing` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.OpenClosedTriangle` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDual` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Same map by proved transport equality; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Same map by proved transport equality; no adaptation. |

## Status

landed 20261021T013343-L-2289028 2026-10-21 (merge of deliver/H4/Sheaf.Paper.CompactSupportSiteCoherence)
