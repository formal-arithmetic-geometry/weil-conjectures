# AlgebraicGeometry.Scheme.tensorPullback_unit_open_localization

## Reason

The static checker requires a change record for proof section commands. Added a scoped noncomputable section, opens for category-theory notation, and transparency options for the private comparison proofs. All existing public signatures and public imports stay identical. All new helpers and instances are private. This records commands, not a changed mathematical interface. No target statement or definition changes and no forced adaptation is needed. The sole direct declaration user, FiniteLocallyFreeTensorUnit, still applies the identical existential theorem and receives the same H, α, θ fields.

## Old

```lean
theorem tensorPullback_unit_open_localization {X Y : Scheme.{u}} (p : X ⟶ Y)
    (U : Opens Y) :
    ∃ (H : SheafOfModules.{u} (Y.ringCatSheaf.over U) ⥤
        SheafOfModules.{u} (Y.ringCatSheaf.over U))
      (α : 𝟭 _ ⟶ H)
      (θ : SheafOfModules.overFunctor Y.ringCatSheaf U ⋙ H ≅
        Modules.tensorPullback p ⋙ Modules.pushforward p ⋙
          SheafOfModules.overFunctor Y.ringCatSheaf U),
      H.Additive ∧ ∀ M : Y.Modules,
        ((Classical.choose (Modules.exists_tensorPullbackAdjunction p)).unit.app M).over U =
          α.app (M.over U) ≫ θ.hom.app M
```

## New

```lean
theorem tensorPullback_unit_open_localization {X Y : Scheme.{u}} (p : X ⟶ Y)
    (U : Opens Y) :
    ∃ (H : SheafOfModules.{u} (Y.ringCatSheaf.over U) ⥤
        SheafOfModules.{u} (Y.ringCatSheaf.over U))
      (α : 𝟭 _ ⟶ H)
      (θ : SheafOfModules.overFunctor Y.ringCatSheaf U ⋙ H ≅
        Modules.tensorPullback p ⋙ Modules.pushforward p ⋙
          SheafOfModules.overFunctor Y.ringCatSheaf U),
      H.Additive ∧ ∀ M : Y.Modules,
        ((Classical.choose (Modules.exists_tensorPullbackAdjunction p)).unit.app M).over U =
          α.app (M.over U) ≫ θ.hom.app M
```

The new signature is verbatim identical; only its proof and scoped proof commands change.

## Users

All transitive downstream modules from tools/downstream.py are listed below; none needs adaptation because their importer-visible declarations and imports are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteLocallyFreeTensorUnit | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardPullbackBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardPullbackBaseChangeDual | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardPullbackBaseChangePrimal | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardPullbackLocalRanks | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Signature and public imports unchanged; no adaptation |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Signature and public imports unchanged; no adaptation |
| TargetsCheck | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.FourierTransform.Defs | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.FourierTransform.Properties | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Signature and public imports unchanged; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Signature and public imports unchanged; no adaptation |

## Status

landed 20261013T011928-L-2763595 2026-10-13 (merge of deliver/K2/Sheaf.AlgebraicGeometry.TensorUnitOpenLocalization)
