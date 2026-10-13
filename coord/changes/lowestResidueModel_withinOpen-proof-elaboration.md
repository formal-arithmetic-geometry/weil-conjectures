# AlgebraicGeometry.Scheme.lowestResidueModel_withinOpen: proof elaboration commands

## Reason

The supplied theorem is proved without changing any statement or public import.
Lean distinguishes Scheme.Modules category instances from the project's shared
SheafOfModules instances. A private typed wrapper of the existing restrictFunctor
and three private local instances transport the existing additivity and exactness
facts, ensuring the same shared derived category is used throughout.
Two transparency options and local instance attributes support elaboration of the
comparison functors. The delivery tool conservatively classifies new file commands
as an interface change and requires this record. Every added instance is local;
no new global instance or public definition is introduced in the item's module.
The new residue lemma lives in its own module, imported for the proof only.

## Old

The existing file commands, verbatim:

```lean
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
```

The existing signature of lowestResidueModel_withinOpen is unchanged, verbatim;
its former body was `:= by sorry`.

## New

The proof-elaboration header and private wrapper, verbatim:

```lean
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

-- Use the shared SheafOfModules category instances, rather than Scheme.Modules instances.
private noncomputable def openRestrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := Modules.restrictFunctor f

private local instance openRestrict_additive {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : (openRestrict f).Additive :=
  inferInstanceAs (Modules.restrictFunctor f).Additive

private local instance openRestrict_limits {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : PreservesFiniteLimits (openRestrict f) :=
  inferInstanceAs (PreservesFiniteLimits (Modules.restrictFunctor f))

private local instance openRestrict_colimits {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : PreservesFiniteColimits (openRestrict f) :=
  inferInstanceAs (PreservesFiniteColimits (Modules.restrictFunctor f))
```

The public theorem's signature and visibility are unchanged. The new residue module
has only proved declarations and uses private local stalk instances.

## Users

Computed by tools/downstream.py for the item. No consumer statement becomes stronger,
weaker or different because only proof terms and file-local elaboration change.
PerfectLowestMatrixCharts is the only direct importer and the only downstream textual
user of lowestResidueModel_withinOpen. No adapted consumer is part of this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.LowestResidueModelWithinOpen | P3 | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLowestMatrixClosedLocus | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| TargetsCheck | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Existing signatures, public imports and meanings unchanged; no adaptation. |

## Status

landed 20261013T115431-L-3359683 2026-10-13 (merge of deliver/P3/Sheaf.AlgebraicGeometry.LowestResidueModelWithinOpen)
