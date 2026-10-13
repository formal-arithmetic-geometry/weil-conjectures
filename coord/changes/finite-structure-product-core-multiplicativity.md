# AlgebraicGeometry.finite_structure_product_exists_core

## Reason

Repair of return E3/H3 (reviewer X-c9aa6, head c9aa69019). The old Lean conclusion
only asserted existence of an arbitrary morphism and omitted the node's essential
multiplicativity condition. A zero morphism cannot satisfy that condition in general:
for the identity finite map over a nonzero field and I = 0, the adjoint is the identity
and x = y = 1 would require 0 = 1. Restore the interface requested by the reviewer.
The adjoint function has an explicit structure-sheaf section codomain (as in
ProductExists), so Lean sees the section ring multiplication. This is the same
adjoint and formula required by the return. The compatible-product construction remains unresolved, with a named theorem `sorry`.
No target signature or definition changes. The node's mathematical statement already
contains multiplicativity and is unchanged; its `lean.statement` is corrected.

## Old

```lean
theorem finite_structure_product_exists_core
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm)
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1)))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G)
    (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅
        (Scheme.Modules.pushforward (fnY n)).obj
          (SheafOfModules.unit (Yn n).ringCatSheaf))
    (hψ : ∀ n,
      (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
        (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
          (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
          (Scheme.Modules.pushforward (fnY n)).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) =
        (c n).hom.app G ≫ (ψ n).hom) :
    Nonempty (G ⊗ G ⟶ G)
```

## New

```lean
theorem finite_structure_product_exists_core
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm)
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1)))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G)
    (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅
        (Scheme.Modules.pushforward (fnY n)).obj
          (SheafOfModules.unit (Yn n).ringCatSheaf))
    (hψ : ∀ n,
      (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
        (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
          (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
          (Scheme.Modules.pushforward (fnY n)).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) =
        (c n).hom.app G ≫ (ψ n).hom) :
    ∃ μ : G ⊗ G ⟶ G, ∀ (n : ℕ) (U : X.Opens),
      let a : Γ(G, U) → Γ(Yn n, (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U) :=
        fun x ↦ (Scheme.Modules.finiteStructureAdjoint
        (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U x
      ∀ (x y : Γ(G, U)), a (μ.app U (tmulSection x y)) = a x * a y
```

## Users

The downstream tool lists 199 transitive importers. Its `--uses` search finds only
Core itself and ProductExists mentioning the declaration. All are listed below.
No user signature changes; no forced adaptations are delivered. The original direct
importers are compiled against the repaired interface before the dry run.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteStructureProductCore | U4 | owned interface repaired; compatible existence unresolved |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.Paper.FiniteStructureAlgebraAdjointsConstruct | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.Paper.FiniteStructureAlgebraLift | D2 | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.Paper.FiniteStructureMultiplicationLift | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.Paper.FiniteStructureProductCompatibility | U4 | direct public importer; no use of core theorem; statement unchanged |
| Sheaf.Paper.FiniteStructureProductExists | unclaimed | only external declaration use; unchanged existential pattern tested against repaired core; public statement unchanged |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| TargetsCheck | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.FourierTransform.Defs | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.FourierTransform.Inversion | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.FourierTransform.Perverse | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.FourierTransform.Properties | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | transitive importer; no reference to core theorem; statement unchanged |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | transitive importer; no reference to core theorem; statement unchanged |

## Status

landed 20261013T160713-L-1372552 2026-10-13 (merge of deliver/U4/Sheaf.Paper.FiniteStructureProductCore)
