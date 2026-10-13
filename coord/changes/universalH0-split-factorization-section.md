# CochainComplex.universalH0_split_factorization

## Reason

The equation e r=id_(P^0) is false: take R=Z and the complex R concentrated in degree zero. The differential is zero but the two claimed retractions would imply id_R=e r=e(p q)r=(e p)q r=0. Reverse the first splitting equation to r e=id_I, the section equation for the surjection onto the image. The original algebraic contradiction is also certified in scratchpad/Counterexample.lean. This is an intermediate statement correction, not a target change.

The source is the image/quotient splitting argument of [Stacks Tag 00NX](https://stacks.math.columbia.edu/tag/00NX), following the unit-minor calculation of [Tag 00O0](https://stacks.math.columbia.edu/tag/00O0). This corrects a transcription in our helper, not the source. No Challenge statement or public definition changes.

## Old

```lean
theorem universalH0_split_factorization (R : Type v) [CommRing R] (P : CochainComplex (ModuleCat.{v} R) ℤ) (hf0 : Module.Finite R (P.X 0)) (hf1 : Module.Finite R (P.X 1)) (hp0 : Module.Projective R (P.X 0)) (hp1 : Module.Projective R (P.X 1)) (hneg : IsZero (P.X (-1))) (hzero : ∀ (B : Type v) [CommRing B] (φ : R →+* B), let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) : ∃ (I : ModuleCat.{v} R) (e : P.X 0 ⟶ I) (p : I ⟶ P.X 1) (r : I ⟶ P.X 0) (q : P.X 1 ⟶ I), P.d 0 1 = e ≫ p ∧ e ≫ r = 𝟙 (P.X 0) ∧ p ≫ q = 𝟙 I
```

## New

```lean
theorem universalH0_split_factorization (R : Type v) [CommRing R] (P : CochainComplex (ModuleCat.{v} R) ℤ) (hf0 : Module.Finite R (P.X 0)) (hf1 : Module.Finite R (P.X 1)) (hp0 : Module.Projective R (P.X 0)) (hp1 : Module.Projective R (P.X 1)) (hneg : IsZero (P.X (-1))) (hzero : ∀ (B : Type v) [CommRing B] (φ : R →+* B), let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) : ∃ (I : ModuleCat.{v} R) (e : P.X 0 ⟶ I) (p : I ⟶ P.X 1) (r : I ⟶ P.X 0) (q : P.X 1 ⟶ I), P.d 0 1 = e ≫ p ∧ r ≫ e = 𝟙 I ∧ p ≫ q = 𝟙 I
```

## Users

`tools/downstream.py --uses` found only the item and UniversalH0SplitDifferential mentioning the name. The table includes all 166 transitive downstream modules; their signatures do not mention this proof-only dependency. The caller is unclaimed in this checkout. Its sole changed line is:

```lean
-- old:
rw [← Category.assoc, her, Category.id_comp, hfac]
-- new:
rw [← Category.assoc r e p, her, Category.id_comp, ← hfac]
```

The original fails against the corrected dependency because `her` now has type `r ≫ e = 𝟙 I`, whereas the old rewrite reassociates to `(e ≫ r) ≫ e ≫ p`. The adapted line reassociates only the inner three factors. No other caller line changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.UniversalH0SplitFactorization | N3 | Correct source/image section identity; complete proof from local freeness. |
| Sheaf.Algebra.Homology.ConnectiveUniversalH0ZeroDifferential | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.Algebra.Homology.UniversalH0ProjectiveNormalization | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.Algebra.Homology.UniversalH0SplitDifferential | unclaimed | Forced one-line proof adaptation at line 74; signature and visibility identical. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardAffineTargetNormalization | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| TargetsCheck | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No direct reference to changed declaration; public signatures and definitions unchanged. |

## Status

landed 20261013T165646-L-1809612 2026-10-13 (merge of deliver/N3/Sheaf.Algebra.Homology.UniversalH0SplitFactorization)
