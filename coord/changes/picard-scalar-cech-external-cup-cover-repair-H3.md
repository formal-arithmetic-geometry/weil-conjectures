# picardScalarCech_externalCup_core

## Reason

STATEMENT-DISPUTED: the old helper omitted the open-cover equalities. Its arbitrary canonical-comparison witnesses only constrain restrictions to the listed opens, so extensions outside their union need not preserve the external cup. Restore the cover hypotheses already present in `picardScalarCech_externalCup`; this repairs a false below-unit helper. No Challenge target or definition changes.

Stage-3 repair in the legacy statement_change schema: restore both cover equalities omitted by the false below-unit helper. On P1_k with rational points x0,x1 and U=V=P1 minus x1, take F=G=k(x0) direct-sum k(x1). The global rings are k. Factor comparisons can extend s to (s,0), and a product comparison can extend s to (s,s,s,s), since their defining equations see only restriction to U or U times U. For the classes of 1 the external cup of the factor extensions is (1,0,0,0), whereas the product extension is (1,1,1,1). This is a mathematical counterexample, not a fully Lean-formalized scheme construction. The former disjoint Spec(k times k) example fails because ring-linear maps must respect global idempotents. The public enclosing theorem already assumes both cover equalities and keeps exactly its old signature.

The source requires open covers: [Stacks 01FD](https://stacks.math.columbia.edu/tag/01FD) and [Stacks 0FKV](https://stacks.math.columbia.edu/tag/0FKV). The verified replacement uses their ordinary pairing route, then the existing scalar/module bridge.

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

`tools/downstream.py Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup --uses picardScalarCech_externalCup_core` lists 174 transitive importers and only the item as a textual user of the core. Current holders were read from the server on 2026-10-14; local claim copies are stale. The proof-only imports added here remain private to the module. The two original public imports stay public. Every other declaration and definition has the same signature and meaning. No module outside this item is adapted. The target-statement review is unaffected because no target-used definition changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | H3 | Add hUc,hVc to the core only; its sole local caller supplies them. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | XR69063533eda144cf | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechComparison | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupHomology | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupHomology | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.ProductResidueH1Injective | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| TargetsCheck | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Does not use the core; the enclosing theorem and public imports are unchanged. No adaptation. |

## Status

landed 20261014T111252-L-1842184 2026-10-14 (merge of deliver/H3/Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup)
