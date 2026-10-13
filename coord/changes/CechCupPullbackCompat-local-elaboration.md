# Sheaf.Paper.CechCupPullbackCompat local elaboration controls

## Reason

The complete composition proof needs local elaboration controls to keep tensor-pullback
constructions from expanding during section and scalar-instance calculations. The instance
priority matches `Sheaf.AlgebraicGeometry.EtaleTensorSections`. The static preflight flags
attribute commands even when their attributes are local, so this record documents them.
All existing definitions, statements, universes, visibility and public imports stay identical.
The new import is proof-only. No target's meaning changes.

## Old

No local irreducibility or section-scalar-instance priority attributes in this module.
The composition theorem had the whole proof `:= by sorry` and no scoped linter or
heartbeat options. The two already proved substantial naturality theorems retain their
existing scoped heartbeat options.

## New

Immediately inside the noncomputable section:

```lean
-- Keep section scalar instances at the scheme-module interface.
attribute [local irreducible] tensorPullback tensorPullbackObj
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
```

The complete proof of `cechRefinement_composition_naturality` is preceded by:

```lean
-- The intermediate cover hypothesis stays in the signature but is not needed here.
set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- Respect the irreducible pullback interface during the composition calculation.
set_option backward.isDefEq.respectTransparency true in
```

The unused-variable option is scoped to the one theorem because its original `hU'`
binder must remain. Repair H10 makes unification respect irreducibility in the unit
and cochain calculation, and restores `backward.isDefEq.respectTransparency false`
inside the final homology-transport block. This avoids unnecessary expansion of the
concrete pullback construction while retaining the normalization needed by homology
instances. No global option changes. These controls are local to elaboration of this
module; no instance or reducibility attribute is exported. There is no change to a definition body and no
forced adaptation.

## Users

The following table is the source-only `tools/downstream.py` transitive import inventory
at the fetched base. It includes the item itself. The two direct importers are
`Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes` and
`Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram`. Since the attributes are local
and no signature changes, every downstream statement retains its original meaning.
Holders are the current local claim records; no other group's module is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CechCupPullbackCompat | R3 | Local proof elaboration only; unchanged signatures. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProductResidueH1Injective | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No exported change; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No exported change; no adaptation. |
| TargetsCheck | unclaimed | No exported change; no adaptation. |
| WeilConjectures | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No exported change; no adaptation. |

## Status

landed 20261013T150353-L-810197 2026-10-13 (merge of deliver/R3/Sheaf.Paper.CechCupPullbackCompat)
