# AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core

## Reason

STATEMENT-DISPUTED: the core drops both cover hypotheses. For a non-cover,
IsModuleCechComparison fixes a lift through H(alpha), which need not be injective;
two lifts can differ by a map into its kernel. The scalar comparison predicate
inherits this freedom. Consequently the claimed cup compatibility of arbitrary
such lifts is false. Stacks Tags 01FD and 0FKV explicitly assume open coverings.
The earlier reviews recorded the same error (ledger entries 2026-10-13 19:15 and
2026-10-14 01:38). Withdraw this false split, without replacing it by a weaker theorem.
The cover theorem is proved directly from the existing ordinary module Cech
external pairing and scalar external cup comparison, using hUc and hVc.

A concrete geometric counterexample: take a field k and X=P1_k times P1_k.
Let C0 and Cinf be two disjoint fibres of the first projection, and let
F=i0_*O_C0(-2) direct-sum iinf_*O_Cinf(-2). Take the two opens
(P1 minus infinity) times (P1 minus infinity) and
(P1 minus infinity) times (P1 minus zero). Their union misses Cinf and contains
C0. Since Gamma(X,O_X)=k, the module comparisons are k-linear. Their Cech
cohomology for F is k in degree one and zero elsewhere; global H1(X,F)=k^2.
H(alpha) on degree one is projection onto the first coordinate, so either
s maps to (s,0) or s maps to (s,s) satisfies the comparison equation for every
injective resolution. Use the first lift for eX and the second for eP. Take
Y=Spec k, G=O_Y, its one-open cover, q=0, and the unit class. The external
Cech pairing and the external cup with this unit both identify with the
identity on the X factor. Thus the asserted formula would identify (s,0)
and (s,s) for nonzero s. Quasi-coherence holds for both closed-immersion
pushforwards, so the original core hypotheses do not exclude this example.

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
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v))) := by
  sorry
```

## New

The declaration is withdrawn. Its DAG node is retained with lean set to null
and its obsolete proof dependencies cleared. The unchanged-signature theorem
picardScalarCech_externalCup has a complete proof using its original covers;
there is no replacement declaration for the uncovered assertion.

## Users

The source search and tools/downstream.py --uses find only this module using the
core. The table includes every transitive importer returned by tools/downstream.py;
none of them mentions the removed declaration. The direct importer
Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison uses the retained cover
theorem. No definition changes, and no target statement requires semantic re-review.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | P4 | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechComparison | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupHomology | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupHomology | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | F4 | Remove the false core; prove the cover theorem directly. |
| Sheaf.AlgebraicGeometry.ProductResidueH1Injective | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| TargetsCheck | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Does not use the core; existing statements and definitions keep their meaning. |

## Status

landed 20261014T094638-L-809514 2026-10-14 (merge of deliver/F4/Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup)
