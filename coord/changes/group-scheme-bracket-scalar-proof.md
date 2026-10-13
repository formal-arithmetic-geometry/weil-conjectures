# AlgebraicGeometry.GrpObj.instLieAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopLie

## Reason

The interface scanner compares entire instance bodies, including proof fields. This record
therefore accompanies the proof of scalar compatibility. The instance retains exactly its
original type, its inherited module structure, and the same commutator bracket. Only the
proposition-valued `lie_smul` field changes, hence proof irrelevance identifies the old and new
structures. No target statement or mathematical meaning changes.

The declaration follows `lieEquiv_symm_smul` so its proof can use the already-established
rescaling equivalence. Its visibility and generated name are unchanged. The scalar proof is
local to the instance: no private helper occurs in a public definition.

## Old

```lean
noncomputable instance : LieAlgebra Γ(S, ⊤) (Lie G) where
  lie_smul := by sorry
```

## New

```lean
noncomputable instance : LieAlgebra Γ(S, ⊤) (Lie G) where
  lie_smul := by
    intro r x y
    have hs (v w : infPoints G) :
        infBracket G v (infPointsScale G r w) = infPointsScale G r (infBracket G v w) := by
      let d₀ := S.dualNumbers.dualNumbersScale (inl r)
      have dbase : d₀ ≫ (S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj) =
          S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj := by
        simp [d₀]
      let d : Scheme.dualNumbers₂Over S ⟶ Scheme.dualNumbers₂Over S := Over.homMk d₀ dbase
      have he : d ≫ Scheme.dualNumbersProjεOver S = Scheme.dualNumbersProjεOver S := by
        apply Over.OverMorphism.ext
        exact S.dualNumbers.dualNumbersScale_comp_proj (inl r)
      have hd : d ≫ Scheme.dualNumbersProjδOver S =
          Scheme.dualNumbersProjδOver S ≫ Scheme.dualNumbersScaleOver S r := by
        apply Over.OverMorphism.ext
        change d₀ ≫ S.dualNumbersProj.dualNumbers =
          S.dualNumbersProj.dualNumbers ≫ S.dualNumbersScale r
        refine Scheme.Hom.ext rfl fun U ↦ ?_
        simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
        erw [eqToHom_refl, Category.comp_id]
        ext a : 2
        let c := S.presheaf.map (homOfLE le_top : U ⟶ ⊤).op r
        let c₀ := S.dualNumbers.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (inl r)
        change DualNumber.scale c₀ (DualNumber.mapRingHom (inlHom Γ(S, U) Γ(S, U)) a) =
          DualNumber.mapRingHom (inlHom Γ(S, U) Γ(S, U)) (DualNumber.scale c a)
        have hc₀ : c₀ = inl c := by
          change DualNumber.mapRingHom (S.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom
            (inl r) = inl c
          apply TrivSqZeroExt.ext <;> simp [c]
        rw [hc₀]
        apply TrivSqZeroExt.ext
        · apply TrivSqZeroExt.ext
          · simp only [DualNumber.mapRingHom, inlHom_apply, DualNumber.inr_eq_smul_eps,
              RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add, map_smul,
              fst_add, DualNumber.fst_scale, fst_inl, fst_smul, DualNumber.fst_eps,
              smul_eq_mul, mul_zero, add_zero, DualNumber.snd_scale, inl_mul]
          · simp only [DualNumber.mapRingHom, inlHom_apply, DualNumber.inr_eq_smul_eps,
              RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add, map_smul,
              fst_add, DualNumber.fst_scale, fst_inl, fst_smul, DualNumber.fst_eps,
              smul_eq_mul, mul_zero, add_zero, snd_inl, DualNumber.snd_scale, inl_mul]
        · apply TrivSqZeroExt.ext
          · simp only [DualNumber.mapRingHom, inlHom_apply, DualNumber.inr_eq_smul_eps,
              RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add, map_smul,
              snd_add, DualNumber.snd_scale, snd_inl, mul_zero, snd_smul, DualNumber.snd_eps,
              mul_one, smul_eq_mul, zero_add, fst_mul, fst_inl, DualNumber.fst_scale, inl_mul]
            exact mul_comm _ _
          · simp only [DualNumber.mapRingHom, inlHom_apply, DualNumber.inr_eq_smul_eps,
              RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add, map_smul,
              snd_add, DualNumber.snd_scale, snd_inl, mul_zero, snd_smul, DualNumber.snd_eps,
              mul_one, smul_eq_mul, zero_add, snd_mul, fst_inl, smul_zero, add_zero,
              DualNumber.fst_scale, inl_mul]
      have hm : d ≫ Scheme.dualNumbersMulOver S =
          Scheme.dualNumbersMulOver S ≫ Scheme.dualNumbersScaleOver S r := by
        apply Over.OverMorphism.ext
        change d₀ ≫ S.dualNumbersMul = S.dualNumbersMul ≫ S.dualNumbersScale r
        refine Scheme.Hom.ext rfl fun U ↦ ?_
        simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
        erw [eqToHom_refl, Category.comp_id]
        ext a : 2
        let c := S.presheaf.map (homOfLE le_top : U ⟶ ⊤).op r
        let c₀ := S.dualNumbers.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (inl r)
        change DualNumber.scale c₀ (DualNumber.mulRingHom a) =
          DualNumber.mulRingHom (DualNumber.scale c a)
        have hc₀ : c₀ = inl c := by
          change DualNumber.mapRingHom (S.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom
            (inl r) = inl c
          apply TrivSqZeroExt.ext <;> simp [c]
        rw [hc₀]
        apply TrivSqZeroExt.ext
        · rw [DualNumber.fst_scale, DualNumber.fst_mulRingHom, DualNumber.fst_mulRingHom,
            DualNumber.fst_scale]
        · rw [DualNumber.snd_scale, DualNumber.snd_mulRingHom, DualNumber.snd_mulRingHom,
            DualNumber.snd_scale]
          change (inl c : DualNumber Γ(S, U)) * inr a.snd = inr (c * a.snd)
          rw [inl_mul_inr]
          rfl
      have hc (a b : infPoints G) :
          Scheme.dualNumbersMulOver S ≫ (infBracket G a b).1 =
            toε G a * toδ G b * (toε G a)⁻¹ * (toδ G b)⁻¹ :=
        congrArg Subtype.val ((mixedEquiv G).apply_symm_apply _)
      have hε : d ≫ toε G v = toε G v := by
        rw [toε, ← Category.assoc, he]
      have hδ : d ≫ toδ G w = toδ G (infPointsScale G r w) := by
        rw [toδ, ← Category.assoc, hd, Category.assoc]
        rfl
      apply (mixedEquiv G).injective
      apply Subtype.ext
      change Scheme.dualNumbersMulOver S ≫ (infBracket G v (infPointsScale G r w)).1 =
        Scheme.dualNumbersMulOver S ≫ Scheme.dualNumbersScaleOver S r ≫ (infBracket G v w).1
      rw [← Category.assoc, ← hm, Category.assoc, hc, hc]
      change _ = pointsPrecomp G d _
      simp only [map_mul, map_inv, pointsPrecomp_apply, hε, hδ]
    rw [lie_def, lieEquiv_symm_smul, hs, lie_def]
    exact toLie_infPointsScale G r _
```

## Users

Repair X-39192: the query below was rerun read-only on 2026-10-13 using the actual
unqualified generated name. It returned 280 downstream modules and zero textual users.
The four LieRing proof fields now reference the four public named obligation theorems
listed in report.md; their types are exactly the existing field propositions. Thus the
LieRing instance's bracket and additive data also remain identical by proof irrelevance.
No downstream source edit is needed.

`tools/downstream.py WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket --uses
instLieAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopLie` reports 280 downstream modules and zero textual mentions of the actual generated instance name. All downstream
modules are listed below; the inherited module data and bracket remain identical, and proof
irrelevance identifies the changed proof field. No module needs adaptation. Holders are those
in this machine's current coordination snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | D3 | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | H2 | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.IdentityTangentAddition | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.IdentityTangentOperations | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.IdentityTangentTransport | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDualResidue | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.GroupScheme.LieLocalDimension | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.MatrixSubgroupLieBracket | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.MixedCommutatorTangent | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | proof field only; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | proof field only; no adaptation |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | proof field only; no adaptation |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | proof field only; no adaptation |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | proof field only; no adaptation |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | proof field only; no adaptation |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | proof field only; no adaptation |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | proof field only; no adaptation |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | proof field only; no adaptation |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | proof field only; no adaptation |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | proof field only; no adaptation |
| TargetsCheck | unclaimed | proof field only; no adaptation |
| WeilConjectures | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Image | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Lie | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.RankOne | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Weights | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | proof field only; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | proof field only; no adaptation |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | proof field only; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | proof field only; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | proof field only; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | proof field only; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | proof field only; no adaptation |
| WeilConjectures.FourierTransform.Defs | unclaimed | proof field only; no adaptation |
| WeilConjectures.FourierTransform.Inversion | unclaimed | proof field only; no adaptation |
| WeilConjectures.FourierTransform.Perverse | unclaimed | proof field only; no adaptation |
| WeilConjectures.FourierTransform.Properties | unclaimed | proof field only; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | proof field only; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | proof field only; no adaptation |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | proof field only; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | proof field only; no adaptation |

## Status

landed 20261013T022424-L-3217454 2026-10-13 (merge of deliver/Q2/WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket)
