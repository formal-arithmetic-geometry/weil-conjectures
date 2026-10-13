# AlgebraicGeometry.finite_structure_algebra_lift

## Reason

The operations-lifting theorem was corrected by C4 to use the explicit adjunction mate
`tensorPullbackCompositionIso`. A bare `Classical.choice` of a `Nonempty` isomorphism
cannot pin this mate, so the old caller's `hc` cannot justify the operations theorem.
Change only this normalization hypothesis and its statement import; the conclusion,
other hypotheses, universes and name are retained. The affine quotient proof follows
Stacks 09ZT and 01I9, using the existing exactness theorem and the first isomorphism
 theorem. Sources read online: https://stacks.math.columbia.edu/tag/09ZT,
https://stacks.math.columbia.edu/tag/088F and https://stacks.math.columbia.edu/tag/01I9.

The sole declaration user is `Sheaf.Paper.AlgebraizeFiniteStructureAlgebra` (unclaimed).
Its unchanged proof chooses the old `c` and passes `fun _ ↦ rfl` to the corrected `hc`;
this no longer typechecks. Only proof imports, the local `c` construction and the
existence/application glue are adapted. Its public theorem signature is identical.
To keep Grothendieck existence's legacy interface unchanged, extend the ratio of
legacy and explicit comparisons along the invertible closed-pushforward counit to a
natural automorphism of the identity functor of each thickening's module category.
Twist each system transition by its inverse, apply the original existence theorem,
and cancel the automorphism to get comparisons for the original system with the
explicit mate. The caller imports all SupportedThickeningDictionary to reuse its existing
private extend_pullback_automorphism theorem (triangle identity and naturality),
without changing any dictionary declaration or visibility. No arbitrary chosen
isomorphism is asserted equal to a canonical one. No data definition or target changes.

## Old

```lean
theorem finite_structure_algebra_lift
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
    (hc : ∀ n : ℕ, c n = (Classical.choice (Scheme.Modules.nonempty_tensorPullbackComp (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 +
      1)))))))).symm ≪≫ eqToIso (congrArg Scheme.Modules.tensorPullback (hi n)))
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
    ∃ B : X.CommAlgebraSheaf, Nonempty (B.toModule ≅ G) ∧
      ∃ b : ∀ n, B ⟶ 𝒪⁎(fnY n ≫ pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))),
        (∀ (n : ℕ) (U : X.Opens), IsAffineOpen U →
          ∃ e : (B.right.obj.obj (op U) ⧸
              (RingHom.ker ((pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).app U).hom).map
                (B.hom.hom.app (op U)).hom) ≃+*
              Γ(Yn n, (fnY n ≫ pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U),
            ∀ x, e (Ideal.Quotient.mk _ x) = ((b n).right.hom.app (op U)).hom x) ∧
        (∀ (n : ℕ) (U : X.Opens),
          (b (n + 1)).right.hom.app (op U) ≫
            (gn n).appLE ((fnY (n + 1) ≫ pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⁻¹ᵁ U)
              ((fnY n ≫ pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U)
              (by rw [← Scheme.Hom.comp_preimage, hw n]) =
            (b n).right.hom.app (op U))
```

## New

```lean
theorem finite_structure_algebra_lift
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
    ∃ B : X.CommAlgebraSheaf, Nonempty (B.toModule ≅ G) ∧
      ∃ b : ∀ n, B ⟶ 𝒪⁎(fnY n ≫ pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))),
        (∀ (n : ℕ) (U : X.Opens), IsAffineOpen U →
          ∃ e : (B.right.obj.obj (op U) ⧸
              (RingHom.ker ((pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).app U).hom).map
                (B.hom.hom.app (op U)).hom) ≃+*
              Γ(Yn n, (fnY n ≫ pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U),
            ∀ x, e (Ideal.Quotient.mk _ x) = ((b n).right.hom.app (op U)).hom x) ∧
        (∀ (n : ℕ) (U : X.Opens),
          (b (n + 1)).right.hom.app (op U) ≫
            (gn n).appLE ((fnY (n + 1) ≫ pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⁻¹ᵁ U)
              ((fnY n ≫ pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U)
              (by rw [← Scheme.Hom.comp_preimage, hw n]) =
            (b n).right.hom.app (op U))
```

## Users

`tools/downstream.py Sheaf.Paper.FiniteStructureAlgebraLift --uses
finite_structure_algebra_lift` reports the following import users. Its declaration-use
list contains only this item and the sole adapted caller. All remaining modules use
no changed declaration. Neither the five targets nor definitions they use change.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteStructureAlgebraLift | D2 | Correct hc and prove the named hole. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | Forced proof adaptation: normalize its transition system to use the explicit mate; signature and visibility unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| TargetsCheck | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No declaration use; private import boundary preserves its existing statements and public environment. |

## Status

landed 20261013T155931-L-1301625 2026-10-13 (merge of deliver/D2/Sheaf.Paper.FiniteStructureAlgebraLift)


## Reviewer repair (X-28b69)

The caller now imports `all Sheaf.AlgebraicGeometry.SupportedThickeningDictionary` and
reuses its existing private `extend_pullback_automorphism` theorem. The duplicated local
helper theorem and the old `ClosedImmersionPushforwardFullyFaithful` import were deleted;
the call site uses the dictionary helper directly. No dictionary declaration or visibility
was changed.
