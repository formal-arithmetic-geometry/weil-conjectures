# AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core

## Reason

Tags 01FD and 0FKV assume genuine open covers. Without a cover, the equation in
IsModuleCechComparison can characterize a splitting of restriction rather than
a unique canonical map. For example, take X=P1 over k, distinct rational points
x,y, F the direct sum of their skyscraper modules, U={X minus y}, Y=Spec k and
G=k. Global sections of F are k² but sections on U are k. Restriction is first
projection. Both a↦(a,0) and a↦(a,a) split it and satisfy the comparison equation
in degree zero; higher cohomology is zero. Choosing the two different splittings
for the factor and product comparisons violates compatibility with the unit cup.
The clopen version of this example would fail because global idempotents force
the omitted component to vanish; connected X has global functions k. Restore
the cover hypotheses on the internal helper. No target or definition changes.

## Old

```lean
theorem picardScalarCech_externalCup_core
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCechCupComponent f g U V F G c)
    (eX : ∀ p : ℕ, ((picardCechFunctor f U).obj F).homology p →ₗ[k]
      scalarCohomology f F p)
    (heX : ∀ p, IsPicardScalarCechComparison f U F p (eX p))
    (eY : ∀ q : ℕ, ((picardCechFunctor g V).obj G).homology q →ₗ[k]
      scalarCohomology g G q)
    (heY : ∀ q, IsPicardScalarCechComparison g V G q (eY q))
    (eP : ∀ n : ℕ,
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).homology n →ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n)
    (heP : ∀ n, IsPicardScalarCechComparison (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) n (eP n)) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
    T.iCycles n z = HomologicalComplex.ιMapBifunctor A B
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ) i.val.1 i.val.2 n
        i.property ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
      eP n (HomologicalComplex.homologyMap c n (T.homologyπ n z)) =
        cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) d)) i.property)
          (externalCup f g F G i.val.1 i.val.2
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v)))
```

## New

```lean
theorem picardScalarCech_externalCup_core
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCechCupComponent f g U V F G c)
    (eX : ∀ p : ℕ, ((picardCechFunctor f U).obj F).homology p →ₗ[k]
      scalarCohomology f F p)
    (heX : ∀ p, IsPicardScalarCechComparison f U F p (eX p))
    (eY : ∀ q : ℕ, ((picardCechFunctor g V).obj G).homology q →ₗ[k]
      scalarCohomology g G q)
    (heY : ∀ q, IsPicardScalarCechComparison g V G q (eY q))
    (eP : ∀ n : ℕ,
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).homology n →ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n)
    (heP : ∀ n, IsPicardScalarCechComparison (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) n (eP n)) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
    T.iCycles n z = HomologicalComplex.ιMapBifunctor A B
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ) i.val.1 i.val.2 n
        i.property ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
      eP n (HomologicalComplex.homologyMap c n (T.homologyπ n z)) =
        cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) d)) i.property)
          (externalCup f g F G i.val.1 i.val.2
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v)))
```

## Users

A textual declaration search finds only the caller in the same module. The
transitive import users below retain all statement and definition meanings.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | P3 | Pass both existing cover hypotheses to core; outer signature unchanged. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | N3 | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechComparison | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupHomology | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupHomology | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProductResidueH1Injective | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| TargetsCheck | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No direct use of the core; exported outer theorem and all definitions unchanged. |

## Status

landed 20261014T090921-L-366912 2026-10-14 (merge of deliver/P3/Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup)
