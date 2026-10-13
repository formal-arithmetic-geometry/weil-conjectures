# picardDirectImageUnitMorphism_pullback local elaboration attributes

## Reason

The original signature and visibility are unchanged. Elaborating and serializing its
proof repeatedly expands the large tensor-pullback construction. The scoped local
irreducibility attributes prevent that expansion only while checking this declaration.
The delivery parser classifies this scoped command as an interface command change,
so this record documents it. Neither definition body nor downstream reducibility changes.

## Old

The original theorem signature, without a scoped local irreducibility attribute:

```lean
theorem picardDirectImageUnitMorphism_pullback
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (h : i ≫ t = t')
        (j : pullback f (t' ≫ k) ⟶ pullback f (t ≫ k)),
        ∀ (hj₁ : j ≫ pullback.fst f (t ≫ k) = pullback.fst f (t' ≫ k)),
          j ≫ pullback.snd f (t ≫ k) = pullback.snd f (t' ≫ k) ≫ i →
          let c := (conjugateIsoEquiv
            ((Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t ≫ k)))).comp
                (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
            (Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t' ≫ k))))).symm
            (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
              Modules.pushforwardCongr hj₁)
          ∀ ξ : picardDerivedModelSections E t,
            let U := SheafOfModules.unit
              (moduleRings (pullback f (t ≫ k)).toRingedSpace)
            let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction j)
            (adj.leftAdjointUniq (Modules.pullbackPushforwardAdjunction j)).hom.app U ≫
                SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom ≫
                picardDirectImageUnitMorphism f L W k t'
                  (picardDerivedModelRestriction E i t t' h ξ) =
              (Modules.tensorPullback j).map
                (picardDirectImageUnitMorphism f L W k t ξ) ≫ (c.app L).inv
```

## New

```lean
attribute [local irreducible] Modules.tensorPullback picardDirectImageUnitMorphism in
theorem picardDirectImageUnitMorphism_pullback
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (h : i ≫ t = t')
        (j : pullback f (t' ≫ k) ⟶ pullback f (t ≫ k)),
        ∀ (hj₁ : j ≫ pullback.fst f (t ≫ k) = pullback.fst f (t' ≫ k)),
          j ≫ pullback.snd f (t ≫ k) = pullback.snd f (t' ≫ k) ≫ i →
          let c := (conjugateIsoEquiv
            ((Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t ≫ k)))).comp
                (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
            (Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t' ≫ k))))).symm
            (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
              Modules.pushforwardCongr hj₁)
          ∀ ξ : picardDerivedModelSections E t,
            let U := SheafOfModules.unit
              (moduleRings (pullback f (t ≫ k)).toRingedSpace)
            let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction j)
            (adj.leftAdjointUniq (Modules.pullbackPushforwardAdjunction j)).hom.app U ≫
                SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom ≫
                picardDirectImageUnitMorphism f L W k t'
                  (picardDerivedModelRestriction E i t t' h ξ) =
              (Modules.tensorPullback j).map
                (picardDirectImageUnitMorphism f L W k t ξ) ≫ (c.app L).inv
```

This command scopes over the existing theorem with its exact original signature.
No target statement or definition meaning changes and no target review is reopened.

## Users

The following are the complete downstream module list from tools/downstream.py.
The only direct theorem user is PicardDirectImageSectionMapRestriction; no adaptation
is necessary because the local attribute ends at the theorem declaration.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback` | S1 | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.GeneralTheoremOfCube` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageTestSections` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardH1IntersectionSection` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalDescent` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardH1MultipleLocus` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardProductOpen` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardProductOpenData` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | No effect: attributes are local to the proof declaration. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | No effect: attributes are local to the proof declaration. |
| `TargetsCheck` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Final` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.Curve.Estimate` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.AlgebraicGeometry.TheoremOfCube` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | ORCHESTRA | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | No effect: attributes are local to the proof declaration. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | No effect: attributes are local to the proof declaration. |

## Status

landed 20261013T172658-L-2100781 2026-10-13 (merge of deliver/S1/Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback)
