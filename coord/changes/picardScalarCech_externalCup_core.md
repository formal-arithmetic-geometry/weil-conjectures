# AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core

## Reason

The concurrent S1 landing removed both cover equalities from the core theorem.
STATEMENT-DISPUTED (old version): comparison witnesses on noncovers need not be
multiplicative away from the union of the chosen opens. For X=Y the disjoint union
of two copies of Spec k, take U and V to be the first component alone, and F=O_X,
G=O_Y in degree zero. Let eX and eY extend a section on the first component by zero
on the second. Let eP extend the section on component (1,1) also to component (2,2).
These maps satisfy the comparison characterization: after restricting to the
selected opens, each is the same identity. The condition for every resolution
still sees only these restrictions. But for a=b=1, the product comparison gives
value 1 on (2,2), whereas externalCup of the factor extensions gives value zero
there. Thus the core equality fails. Tags 01FD and 0FKV explicitly use open covers.

Restore the same cover hypotheses already present in the enclosing theorem,
then prove the corrected core using the two strictly separate intermediate
statements. The enclosing theorem's existing signature is unchanged and its
call passes its two existing cover hypotheses. This changes a helper statement,
not any Challenge target or definition. No target meaning is changed. The new
local irreducibility annotations affect proof elaboration only.

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

`downstream.py --uses picardScalarCech_externalCup_core` finds only the item itself
using this declaration. The full import-descendant list is recorded below as well.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | A4 | Core corrected and proved; existing main theorem passes its existing cover hypotheses. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechComparison | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupHomology | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupHomology | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProductResidueH1Injective | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| TargetsCheck | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No core use; all existing statements and definitions unchanged; no adaptation. |

## Status

landed 20261013T165637-L-1806853 2026-10-13 (merge of deliver/A4/Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup)
