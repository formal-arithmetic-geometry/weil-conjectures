# CategoryTheory.sheaf_cech_augmentation_quasiIsoAt_zero

## Reason

The target needs abelian-group homology and the sheaf definition, but does not use the general sheaf-cohomology or Ext development. Replace its broad public import with the smaller modules providing exactly those signature objects and instances. A plain import of the new proved cocycle-compatibility module supplies its proof helper. No declaration signature or definition changes. This record documents the public-import pruning required by the stage-3 preflight.

## Old

```lean
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
```

The old declaration signature is:

```lean
theorem sheaf_cech_augmentation_quasiIsoAt_zero
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasFiniteWidePullbacks C]
    (I : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X)
    (e : (CochainComplex.single₀ AddCommGrpCat.{v}).obj (I.obj.obj (op X)) ⟶
      (cechComplexFunctor (fun i ↦ Over.mk (π i))).obj ((Over.forget X).op ⋙ I.obj))
    (he : ∀ t : Fin 1 → ι,
      e.f 0 ≫ Pi.π (fun s : Fin 1 → ι ↦
        I.obj.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) t =
          I.obj.map (∏ᶜ (fun k ↦ Over.mk (π (t k)))).hom.op) : QuasiIsoAt e 0
```

## New

```lean
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Sheaf
import Sheaf.CategoryTheory.CechZeroCocycleCompatibility
```

The unchanged declaration signature is:

```lean
theorem sheaf_cech_augmentation_quasiIsoAt_zero
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasFiniteWidePullbacks C]
    (I : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X)
    (e : (CochainComplex.single₀ AddCommGrpCat.{v}).obj (I.obj.obj (op X)) ⟶
      (cechComplexFunctor (fun i ↦ Over.mk (π i))).obj ((Over.forget X).op ⋙ I.obj))
    (he : ∀ t : Fin 1 → ι,
      e.f 0 ≫ Pi.π (fun s : Fin 1 → ι ↦
        I.obj.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) t =
          I.obj.map (∏ᶜ (fun k ↦ Over.mk (π (t k)))).hom.op) : QuasiIsoAt e 0
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.SheafCechAugmentationDegreeZero --uses CategoryTheory.sheaf_cech_augmentation_quasiIsoAt_zero` listed 177 transitive importers. Only `Sheaf.CategoryTheory.InjectiveCechAugmentationQuasiIso` directly imports the changed module, using a proof-only import, and it independently publicly imports `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`. Thus the import pruning has no effect on the declarations available to that direct importer, and the proof-only import prevents the target module's exports from propagating farther. All existing theorem signatures and definitions stay unchanged, so their meanings stay unchanged. The unchanged direct importer is compiled locally against the repaired module; no adaptations are needed. All listed transitive users appear below; holder information is the local claim snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts | Z2 | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.CechH1Injective | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyComparison | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentSourceComparisonNatural | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNatural | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNaturalSucc | K1 | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLift | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerObstruction | R3 | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.CategoryTheory.CechResolutionTotal | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.CategoryTheory.InjectiveCechAugmentationQuasiIso | unclaimed | Unchanged source compiles against repaired module; already publicly imports SheafCohomology.Basic itself. |
| Sheaf.CategoryTheory.InjectiveCechTotalSections | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.CategoryTheory.Sites.SheafCohomology.CechGeneral | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.CategoryTheory.Sites.SheafCohomology.CechGeneralTotal | U2 | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.Paper.BoundaryDerivationSquareZero | Z2 | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| TargetsCheck | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Brauer | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | S2 | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged statements and definitions; proof dependency only beyond the direct importer. |

## Status

landed 20261012T194123-L-458930 2026-10-12 (merge of deliver/M1/Sheaf.CategoryTheory.SheafCechAugmentationDegreeZero)
