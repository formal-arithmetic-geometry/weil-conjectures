# AlgebraicGeometry.Scheme.picardCoefficientTranspose

## Reason

H10 returned the prior delivery because the coefficient-pasting file exceeded
60 seconds, both in the prescribed compilation and the isolated retry. Profiling
reproduced the failure and found about 40 seconds in kernel type checking. The
specialized coefficient-coherence conversion repeatedly expanded large chosen
adjunction and single-functor expressions at fibre products. Inferred single
functors also used the scheme-module presentation instead of explicitly naming
the shared sheaf-of-modules category.

The repair gives the coefficient morphism and counit presentation irreducible,
explicitly typed constructions with proved defining equations and composition
APIs. Coherence is checked on general scheme parameters before the constructions
are specialized to the fibre products. The original theorem signature, the fixed
lift, the fixed adjunction choices, and the morphism are preserved. No compilation
limit is changed and all of the original five modules remain in the delivery.

The equality to the original inverse-Hom presentation is certified by the proved
`coefficientMate_evaluation` helper in the forced factorization adaptation, using
adjunction naturality, the inverse-Hom/counit formula and the fixed mate evaluation.
The API equations are reflexivity or the existing composition theorem; no data
comes from an arbitrary unproved existence claim.

Targets using this definition require renewed stage-2 semantic review under
AGENTS.md §4. Their signatures and mathematical meanings do not change; no target
is claimed sorry-free by this delivery.

## Old

```lean
@[irreducible]
def picardCoefficientTranspose {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
  ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback (pullback.snd f (r ≫ k))).obj
      ((derivedPullback r).obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L)))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (r ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L) :=
  fun {V : Scheme.{v}} (r : V ⟶ W) ↦ by
    let M := (Modules.tensorPullback (pullback.fst f k)).obj L
    let N := (Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L
    let a : pullback f (r ≫ k) ⟶ pullback f k :=
      pullback.lift (pullback.fst f (r ≫ k)) (pullback.snd f (r ≫ k) ≫ r)
        (by rw [Category.assoc]; exact pullback.condition)
    have ha : a ≫ pullback.fst f k = pullback.fst f (r ≫ k) := pullback.lift_fst ..
    have hb : a ≫ pullback.snd f k = pullback.snd f (r ≫ k) ≫ r := pullback.lift_snd ..
    let c := (conjugateIsoEquiv
      ((Classical.choose (Modules.exists_tensorPullbackAdjunction (pullback.fst f k))).comp
        (Classical.choose (Modules.exists_tensorPullbackAdjunction a)))
      (Classical.choose (Modules.exists_tensorPullbackAdjunction
        (pullback.fst f (r ≫ k))))).symm
      (Modules.pushforwardComp a (pullback.fst f k) ≪≫ Modules.pushforwardCongr ha)
    let d : (Modules.pullback a).obj M ≅ N :=
      ((Classical.choose (Modules.exists_tensorPullbackAdjunction a)).leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction a)).symm.app M ≪≫ (c.app L).symm
    let B := schemeDerivedBaseChangeMap (pullback.snd f k) (pullback.snd f (r ≫ k))
      r a hb ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (schemeDerivedDirectImage (pullback.snd f (r ≫ k))).map
          (Modules.canonicalSinglePullbackMap a M ≫
            (DerivedCategory.singleFunctor _ 0).map d.hom)
    let p := pullback.snd f (r ≫ k)
    let adj := Classical.choose (exists_schemeDerivedAdjunction p
      (hAdd := (Classical.choose exists_derivedPullbackComposition) p)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) p)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) p))
    exact (adj.homEquiv _ _).symm B
```

## New

```lean
@[irreducible]
def picardCoefficientTranspose {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
  ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback (pullback.snd f (r ≫ k))).obj
      ((derivedPullback r).obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L)))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (r ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L) :=
  fun {V : Scheme.{v}} (r : V ⟶ W) ↦ by
    let M := (Modules.tensorPullback (pullback.fst f k)).obj L
    let a : pullback f (r ≫ k) ⟶ pullback f k :=
      pullback.lift (pullback.fst f (r ≫ k)) (pullback.snd f (r ≫ k) ≫ r)
        (by rw [Category.assoc]; exact pullback.condition)
    have ha : a ≫ pullback.fst f k = pullback.fst f (r ≫ k) := pullback.lift_fst ..
    have hb : a ≫ pullback.snd f k = pullback.snd f (r ≫ k) ≫ r := pullback.lift_snd ..
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj M
    exact coefficientCounitTranspose (pullback.snd f k)
      (pullback.snd f (r ≫ k)) r a hb K _
      (tensorSingleCoefficientMap (pullback.fst f k)
        (pullback.fst f (r ≫ k)) a ha L)
```

The irreducible `coefficientCounitTranspose` constructs the same square comparison,
pulled-back counit and coefficient map, with a proved defining equation.
`tensorSingleCoefficientMap` constructs the same single-pullback map followed by
single of the fixed coefficient isomorphism, with the shared sheaf category
explicit in its source and target. Its defining equation and composition API are
proved from the existing coefficient-composition statement. The counit pasting
API is proved in this same file on general scheme squares before specialization
at fibre products. No proof is moved to another file to evade the limit, and no
additional hole is introduced by any API equation or pasting calculation.

`TensorCoefficientComparison` also gives the fixed selected adjunctions small
categorical types and proves `tensorCoefficientComparison_eq` displaying the
original expression. All choices are the original choices, obtained from the
already proved tensor-adjunction theorem. The factorization adaptation rewrites
these equations and proves equality with the original inverse-Hom construction
by `coefficientMate_evaluation`. All existing signatures and visibility stay
identical. The two direct importers are checked against the compiled delivery.

## Users

Enumerated every transitive module with `tools/downstream.py
Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting --uses
picardCoefficientTranspose --names` and inspected the direct textual users.
Only the normalized-transpose factorization unfolds the construction in a proof;
its necessary adaptation is included. The downstream pasting theorem uses the
coefficient pasting statement, whose type is unchanged. The other modules import
these declarations transitively: equality of the morphism preserves their meaning.
The existing module's interface and all affected target statements are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting | A4 | Definition optimized; existing theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | T3 | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization | unclaimed | Forced proof adaptation: unfolding gives the counit presentation instead of inverse Hom; signature unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposePasting | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| TargetsCheck | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same morphism by adjunction evaluation; all mathematical statements unchanged. |

## Forced proof adaptation

The original factorization compiled against the unchanged baseline in 29.8 s,
then failed at line 89 against this delivery in 8.1 s:
```
error: typeclass instance problem is stuck
  Category.{?u.214, ?u.216} ?m.275
```
The adapted factorization compiled in 33.5 s. Every existing signature and
visibility is unchanged. The old last line `exact transpose_three_maps _ _ _ _`
is replaced by its transitive combination with the equal counit presentation:
```
  refine (transpose_three_maps _ _ _ _).trans ?_
  congr 1
  rw [coefficientCounitTranspose_eq, tensorSingleCoefficientMap_eq,
    Modules.tensorCoefficientComparison_eq]
  exact coefficientMate_evaluation _ _ _ _ _ _ _ _
```
The added private helper proves that evaluation by adjunction naturality, the
inverse-Hom/counit identity, `schemeDerivedMate_evaluation` and associativity.
Both `backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` retain their original `false` values.
H2 confirmed the helper and API rewrites compile with these settings; the earlier
claim that changing them was necessary is withdrawn. Only the helper and final
proof rewrite are forced by the equal definition-body repair.
The other direct importer is untouched and compiled against the delivery in 51.0 s.

## Status

landed 20261014T013032-L-3411915 2026-10-14 (merge of deliver/A4/Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting)
