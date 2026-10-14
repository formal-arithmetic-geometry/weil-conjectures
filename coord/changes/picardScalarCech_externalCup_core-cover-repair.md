# picardScalarCech_externalCup_core

## Reason

STATEMENT-DISPUTED (baseline, repaired): the helper omitted the cover equalities.
The enclosing public theorem already requires both. Restore them on this below-unit
helper and pass them in its sole local call. No target statement or target definition
changes. No other module needs adaptation.

The corrected counterexample from the route audit uses X = Y = P¹_k, with distinct
k-rational points x0,x1, singleton families U = V = {P¹ minus x1}, and
F = G = k(x0) direct-sum k(x1). Global structure rings are k. The factor comparisons
can extend s as (s,0), and the product comparison can extend s as (s,s,s,s).
Restriction to U or U×U makes these satisfy the defining comparison equation,
whereas the cup of the factor extensions of 1 is (1,0,0,0). Thus the cover-free
core is false. This is the informal geometric example from G3, not a formal Lean
counterexample. The earlier disjoint Spec(k×k) example is invalid: its global-ring
idempotents constrain linearity.

[Stacks 01FD](https://stacks.math.columbia.edu/tag/01FD) and
[Stacks 0FKV](https://stacks.math.columbia.edu/tag/0FKV) explicitly require open covers.
The direct proof uses the existing ordinary pairing and scalar/module bridge;
it introduces no new intermediate statement with sorry. The choice of ordinary cup
comes from a unique-existence theorem, so it is determined by its characterization.

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

The sole caller changes from
`picardScalarCech_externalCup_core f g F G U V c hc ...` to
`picardScalarCech_externalCup_core f g F G U V hUc hVc c hc ...`.
The two public imports are preserved. Added proof imports are PicardExternalCechCupBidegree,
PicardModuleCechExternalPairing, ScalarExternalCupModuleComparison and
ModuleCohomologyCupProduct. The unused plain CechCupPullbackCompat import is removed.
The private moduleCup_congr helper is fully proved. Local irreducibility and the
elaboration options keep derived constructions folded without changing definitions.

## Users

Read-only downstream.py --uses found one module mentioning the core: this item.
For completeness the table also lists all transitive importers from the repository
snapshot. Their statements and definitions do not mention the corrected core.
The brief assigns this item to K4; the cached claim file names XR271e7d0db684643a.
No other group's module is edited. Ownership is left to the normal delivery checks.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | K4 (brief assignment) | Sole direct caller passes existing hUc and hVc. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | P4 | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechComparison | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupHomology | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupHomology | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProductResidueH1Injective | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No use of the core; public theorem and definitions unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No use of the core; public theorem and definitions unchanged. |
| TargetsCheck | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No use of the core; public theorem and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No use of the core; public theorem and definitions unchanged. |

## Status

landed 20261014T104041-L-1453892 2026-10-14 (merge of deliver/K4/Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup)
