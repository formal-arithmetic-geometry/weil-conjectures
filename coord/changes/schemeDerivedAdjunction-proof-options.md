# AlgebraicGeometry.exists_schemeDerivedAdjunction

## Reason

The completed proof requires theorem-local elaboration budgets for the sheaf tensor and
K-flat total-complex instances. Only proof elaboration options change; both the existing
public signature and the base-change definition are identical. No importer needs adaptation.

## Old

```lean
theorem exists_schemeDerivedAdjunction {X Y : Scheme.{uAdj}} (f : X ⟶ Y)
    [HasDerivedCategory.{wAdj} (SheafOfModules.{uAdj} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wAdj} (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace))]
    [hAdd : (Scheme.Modules.tensorPullback f).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh
          (C := SheafOfModules.{uAdj} (moduleRings X.toRingedSpace)))
    (hε : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))) :
    ∃ adj : derivedPullback f ⊣ schemeDerivedDirectImage f,
      ∀ (M : HomotopyCategory
          (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
        (K : HomotopyCategory
          (SheafOfModules.{uAdj} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
        (a : ((Scheme.Modules.tensorPullback f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj M ⟶ K),
        adj.homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj K)
            (ε.app M ≫ DerivedCategory.Qh.map a) =
          (DerivedCategory.Qh
            (C := SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace))).map
            (((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction f)).mapHomotopyCategory
                (ComplexShape.up ℤ)).homEquiv M K a) ≫
            (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K
```

The theorem uses the default maxHeartbeats and synthInstance.maxSize.

## New

```lean
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 800000 in
theorem exists_schemeDerivedAdjunction {X Y : Scheme.{uAdj}} (f : X ⟶ Y)
    [HasDerivedCategory.{wAdj} (SheafOfModules.{uAdj} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wAdj} (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace))]
    [hAdd : (Scheme.Modules.tensorPullback f).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh
          (C := SheafOfModules.{uAdj} (moduleRings X.toRingedSpace)))
    (hε : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))) :
    ∃ adj : derivedPullback f ⊣ schemeDerivedDirectImage f,
      ∀ (M : HomotopyCategory
          (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
        (K : HomotopyCategory
          (SheafOfModules.{uAdj} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
        (a : ((Scheme.Modules.tensorPullback f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj M ⟶ K),
        adj.homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj K)
            (ε.app M ≫ DerivedCategory.Qh.map a) =
          (DerivedCategory.Qh
            (C := SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace))).map
            (((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction f)).mapHomotopyCategory
                (ComplexShape.up ℤ)).homEquiv M K a) ≫
            (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K
```

Both options are scoped to this theorem. No public import is removed or added. No target
statement or definition is changed, so no semantic target review is reopened.

## Users

The downstream script lists the import closure and then textual declaration uses. Every
listed module is included below; the group is not queried because none is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.SingleComplexAffineBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeMapCech | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GenusInvariant | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Picard.ArrowIsoTensorPullbackCounit | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeIsIso | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.PicardProductOpen | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.RelativeMayerVietoris | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | not queried; no edit | unchanged signature and definitions; no adaptation |
| TargetsCheck | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.FourierTransform.Defs | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.FourierTransform.Inversion | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.FourierTransform.Perverse | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.FourierTransform.Properties | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.FourierTransform.Properties.Stalk | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not queried; no edit | unchanged signature and definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not queried; no edit | unchanged signature and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap | not queried; no edit | unchanged signature and definitions; no adaptation |

## Status

landed 20261012T095923-L-324608 2026-10-12 (merge of deliver/S3/Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap)
