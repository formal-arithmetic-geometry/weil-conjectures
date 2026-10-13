# AlgebraicGeometry.Scheme.picardTermwiseModel and picardTermwiseSource

## Reason

The two independent coherence lemmas must refer to the same ordinary complexes as
this module without importing the theorem which depends on them. Move the two
existing abbreviations verbatim into PicardTermwiseModels and publicly import
that module here. Names, universes, signatures, bodies and visibility are identical;
no target meaning changes. The additional restriction isomorphisms and complex
counit are explicit constructions from the existing functor comparisons. The counit
uses the same selected left-derived cone as the pinned derived composition family.
Its universal property determines it up to the compatible isomorphism used here.

## Old

```lean
/-- Termwise tensor pullback of the model transported from the open site.
Source: Stacks Project, Tag 06YJ.
(blueprint: lem-sc-picard-termwise-model-comparison) -/
abbrev picardTermwiseModel (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    {T : Scheme.{v}} (s : T ⟶ U.toScheme) :
    CochainComplex (SheafOfModules.{v} (moduleRings T.toRingedSpace)) ℤ := by
  let : (Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (Modules.tensorPullback s).Additive :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction s)).left_adjoint_additive
  exact ((Modules.tensorPullback s).mapHomologicalComplex (.up ℤ)).obj
    (((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K)

/-- The degree-zero single of the underived pullback of the source structure sheaf.
Source: Stacks Project, Tag 06YJ.
(blueprint: lem-sc-picard-termwise-model-comparison) -/
abbrev picardTermwiseSource {W T : Scheme.{v}} (t : T ⟶ W) :=
  (CochainComplex.singleFunctor
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
      ((Modules.tensorPullback t).obj (SheafOfModules.unit (moduleRings W.toRingedSpace)))

```

## New

The following declarations are in Sheaf.AlgebraicGeometry.PicardTermwiseModels,
re-exported by `public import Sheaf.AlgebraicGeometry.PicardTermwiseModels` from
Sheaf.AlgebraicGeometry.PicardTermwiseModelComparison:

```lean
/-- Termwise tensor pullback of the model transported from the open site.
Source: Stacks Project, Tag 06YJ.
(blueprint: def-sc-picard-termwise-models) -/
abbrev picardTermwiseModel (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    {T : Scheme.{v}} (s : T ⟶ U.toScheme) :
    CochainComplex (SheafOfModules.{v} (moduleRings T.toRingedSpace)) ℤ := by
  let : (Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (Modules.tensorPullback s).Additive :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction s)).left_adjoint_additive
  exact ((Modules.tensorPullback s).mapHomologicalComplex (.up ℤ)).obj
    (((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K)

/-- The degree-zero single of the underived pullback of the source structure sheaf.
Source: Stacks Project, Tag 06YJ.
(blueprint: def-sc-picard-termwise-models) -/
abbrev picardTermwiseSource {W T : Scheme.{v}} (t : T ⟶ W) :=
  (CochainComplex.singleFunctor
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
      ((Modules.tensorPullback t).obj (SheafOfModules.unit (moduleRings W.toRingedSpace)))

```

## Users

No adapted existing module is delivered. All downstream modules retain the same
public declarations; only the source file of the abbreviations changes. The direct
user PicardConnectiveModelComparison requires no source change.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardConnectiveModelComparison | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardScalarDerivedCycles | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| TargetsCheck | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same public definitions, re-exported through the original module; no edits. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same public definitions, re-exported through the original module; no edits. |

## Status

landed 20261013T140823-L-315528 2026-10-13 (merge of deliver/P2/Sheaf.AlgebraicGeometry.PicardTermwiseModelComparison)
