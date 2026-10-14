# AlgebraicGeometry.Scheme.Modules.tensorGradedProjection_boundary

## Reason

The repaired proof applies the existing derived-triangle comparison and naturality.
Matching that abstract result over concrete sheaves otherwise unfolds resolution comparisons
and connecting-map constructions deeply enough to exceed the single-file compile limit.
The added `attribute [local irreducible]` entries keep those maps opaque while the canonical
section boundary is identified by its two defining equations. The proof scopes transparency
options and lowers `maxRecDepth` to 300; it does not raise the compiler time limit.

H10 repair: profiling found that the unchanged statement alone spent about 34 seconds
waiting in `.olean serialization`. The implicit predicate argument of `Classical.choose`
contained the adjunction's full tensor/sheafification unit formula, repeated in inferred
coefficient targets. Reusing `tensorGradedUnit` and explicitly naming the target of
`Iso.addCommGroupIsoToAddEquiv` keeps that formula out of repeated elaborated terms.
The proof now unfolds the coefficient projection directly, names the short complex before
applying congruence, fixes the congruence carrier explicitly, and applies the generic
naturality theorem directly against its expected type. No declaration or file is split;
no compiler limit is increased. The generic helper's signature and proof are unchanged.

The preflight static command scanner conservatively treats changes to attribute commands as
an interface change and requires this record. These entries are expressly `local` and hence
are not exported. Every original declaration retains its complete Lean type by definitional equality.
The two unit expressions and one inferred coefficient target are written compactly;
the complete original source type is checked independently against the repaired theorem. No data
definition changes, so no target statement or meaning changes and no target review reopens.

## Old

Original local attribute commands, verbatim:

```lean
attribute [local irreducible] boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
attribute [local irreducible] RingedSpace.moduleSectionBoundary
  Functor.rightDerived tensorPullback
```

Original theorem signature, verbatim:

```lean
theorem tensorGradedProjection_boundary {X Z : Scheme.{u}} {j : Z ⟶ X}
    [IsClosedImmersion j]
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤)))]
    {L : X.Modules} {n : ℕ} (T : TensorGradedPresentation j L)
    (D : TensorBoundaryComparisonData j L n)
    (hshort : ∀ d : ℕ, (ShortComplex.kernelSequence
      ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (L.tensorPow d))).ShortExact)
    (IA : InjectiveResolution T.I)
    (IB : InjectiveResolution (commAlgebraSheafModule X.sheaf T.B))
    (IC : InjectiveResolution (commAlgebraSheafModule X.sheaf T.C))
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ _).map T.i ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ _).map
      (tensorGradedAlgebraMap T.p) ≫ IC.ι)
    (hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) k)).ShortExact)
    (hΓ : ((ShortComplex.mk α β hαβ).map
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ))).ShortExact)
    (δ' : T.C.right.obj.obj (op ⊤) →+
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I))
    (hboundary : ∀ z : T.C.right.obj.obj (op ⊤), δ' z =
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
          (commAlgebraSheafModule X.sheaf T.C) ≫
        (IC.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0).hom ≫
        hΓ.δ 0 1 rfl ≫
        (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).inv).hom z))
    (e : ℕ) (z : T.C.right.obj.obj (op ⊤)) :
    tensorGradedCoefficientProjection T D e (δ' z) =
      (Iso.addCommGroupIsoToAddEquiv (D.k e)).symm
        (RingedSpace.moduleSectionBoundary X.toRingedSpace
          (ShortComplex.kernelSequence
            ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
              (L.tensorPow (n * (e + 1))))) (hshort (n * (e + 1)))
          (Hom.app (T.q (n * (e + 1))) ⊤ z))
```

## New

Local attributes keep the comparison constructions folded:

```lean
attribute [local irreducible] boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
attribute [local irreducible] RingedSpace.moduleSectionBoundary Functor.rightDerived tensorPullback
  Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
  InjectiveResolution.isoRightDerivedObj DerivedCategory.HomologySequence.δ
  ShortComplex.ShortExact.δ tensorGradedAlgebraMap Functor.mapHomologicalComplex
  Functor.rightDerivedFunctorPlus ShortComplex.ShortExact.singleTrianglePlus
```

The module respects transparency in both signatures and proofs. The theorem retains its
complete elaborated type: the following source writes the existing `tensorGradedUnit`
definition in place of its defining expression and explicitly supplies the already inferred
coefficient target. All binders, hypotheses, universes, visibility and the conclusion stay
identical up to definitional equality.

```lean
theorem tensorGradedProjection_boundary {X Z : Scheme.{u}} {j : Z ⟶ X}
    [IsClosedImmersion j]
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤)))]
    {L : X.Modules} {n : ℕ} (T : TensorGradedPresentation j L)
    (D : TensorBoundaryComparisonData j L n)
    (hshort : ∀ d : ℕ, (ShortComplex.kernelSequence
      (tensorGradedUnit j (L.tensorPow d))).ShortExact)
    (IA : InjectiveResolution T.I)
    (IB : InjectiveResolution (commAlgebraSheafModule X.sheaf T.B))
    (IC : InjectiveResolution (commAlgebraSheafModule X.sheaf T.C))
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ _).map T.i ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ _).map
      (tensorGradedAlgebraMap T.p) ≫ IC.ι)
    (hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) k)).ShortExact)
    (hΓ : ((ShortComplex.mk α β hαβ).map
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ))).ShortExact)
    (δ' : T.C.right.obj.obj (op ⊤) →+
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I))
    (hboundary : ∀ z : T.C.right.obj.obj (op ⊤), δ' z =
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
          (commAlgebraSheafModule X.sheaf T.C) ≫
        (IC.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0).hom ≫
        hΓ.δ 0 1 rfl ≫
        (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).inv).hom z))
    (e : ℕ) (z : T.C.right.obj.obj (op ⊤)) :
    tensorGradedCoefficientProjection T D e (δ' z) =
      (Iso.addCommGroupIsoToAddEquiv
        (Y := AddCommGrpCat.of ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
          (kernel (tensorGradedUnit j (L.tensorPow (n * (e + 1))))))) (D.k e)).symm
        (RingedSpace.moduleSectionBoundary X.toRingedSpace
          (ShortComplex.kernelSequence
            (tensorGradedUnit j (L.tensorPow (n * (e + 1))))) (hshort (n * (e + 1)))
          (Hom.app (T.q (n * (e + 1))) ⊤ z))
```

The kernel-checked scratch theorem `original_signature_check` has the complete original
source signature (including both explicit `Classical.choose` expressions) and its proof is
an application of the repaired theorem to precisely the original arguments. This checks every original argument and the original conclusion against the repaired
theorem; the script forces the kernel environment afterward. The final independent run
succeeded in 17.4 seconds and printed only the three permitted axioms for both theorems.
An exploratory whole-expression meta comparison timed out and is not validation evidence.
No dependency definition is edited and no forced adaptation is required.

## Users

Ran `python3 tools/downstream.py Sheaf.AlgebraicGeometry.SquareZeroTensorGradedBoundaryProjection
--uses tensorGradedProjection_boundary`. It found 166 downstream modules; the only downstream
declaration-name user is `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryGradedRealization`.
That module passes precisely the same presentation, comparison, compatible resolutions,
section map and identification hypotheses and receives precisely the same equality. All
other modules see the same statements and definitions transitively. The table includes every
listed downstream module, including the target checker, because no local attribute is exported.
Claims below were read from this checkout's coordination state; no other claimed file is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedBoundaryProjection | T2 | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLift | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLiftingCriterion | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerObstruction | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryGradedRealization | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryLeibniz | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorPowerBoundary | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| TargetsCheck | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Signature and definitions unchanged; local proof elaboration only. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Signature and definitions unchanged; local proof elaboration only. |

## Status

landed 20261014T041920-L-1154854 2026-10-14 (merge of deliver/T2/Sheaf.AlgebraicGeometry.SquareZeroTensorGradedBoundaryProjection)
