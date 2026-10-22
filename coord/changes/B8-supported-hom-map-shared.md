# AlgebraicGeometry.SupportHomPair.Transport.homMap

## Reason

The profiler identified repeated kernel checking of the expanded derived Hom map
and the elementwise compatibility predicate. Reuse the existing canonical
`Functor.representableTransportHom` definition, and give the exact compatibility
formula the shared definition `AlgebraicGeometry.moduleSupportedHomCompatible` in
the new module-valued transport interface. The assigned public definitions use
these constructions. All normalization, coefficient-change, exchange and coherence
arguments remain in the assigned file; no proof is split into a separate file to
avoid the compiler limit.

Both old/new equations are reflexivity after unfolding the shared definitions. No
existing signature, attribute, hypothesis or conclusion changes. Every original
public import remains verbatim; the shared module-valued transport interface is
publicly imported because the public definitions now use its interface. Its public
imports expose the cocycle and derived Hom-map constructions. No adopted source
library is edited. Targets using these definitions need renewed statement review,
with their meanings preserved by definitional equality.

The source and target Hom spaces use the transparent `SupportHomPair.derivedHom`
type name. Its body is exactly the original Hom type. This avoids repeatedly
computing the universe of that type through the chosen localization; the small
profile test reduced the same checks from 10.5 seconds to 14 milliseconds. The wrapper returns the shared function directly; its final `f` binder remains
named in the Pi type. All argument names, order and binder information stay the same.

## Old

```lean
def Transport.homMap (e : Transport S T B L adj)
    (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ)
    (f : (DerivedCategory.singleFunctor (Sheaf S.topology (ModuleCat.{u + 1} A)) 0).obj
      S.supported ⟶ K.obj⟦a⟧) :
    (DerivedCategory.singleFunctor (Sheaf T.topology (ModuleCat.{u + 1} A)) 0).obj
      T.supported ⟶ (L.mapDerivedCategoryPlus.obj K).obj⟦a⟧ :=
  (DerivedCategory.singleFunctor (Sheaf T.topology (ModuleCat.{u + 1} A)) 0).map
      e.closedIso.inv ≫
    (L.mapDerivedCategorySingleFunctor 0).inv.app S.supported ≫
    L.mapDerivedCategory.map f ≫ (L.mapDerivedCategory.commShiftIso a).hom.app K.obj
```

## New

```lean
def Transport.homMap (e : Transport S T B L adj)
    (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ) :
    (f : S.derivedHom K a) → T.derivedHom (L.mapDerivedCategoryPlus.obj K) a :=
  Functor.representableTransportHom L e.closedIso K a
```

## Users

The listed downstream statements keep their meaning. Literal uses of this declaration
are confined to the assigned module. The new transport module supplies the shared
formula. No existing downstream proof needs an adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SupportedHomPullback` | B8 | Reuses the definitionally equal canonical map and compatibility formula. |
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
