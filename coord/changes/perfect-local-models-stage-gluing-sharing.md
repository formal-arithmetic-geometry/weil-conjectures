# AlgebraicGeometry.perfect_local_models_stage_gluing

## Reason

The original signature repeats the canonical stage scheme, limit scheme and map
in each comparison. An unchanged baseline artifact compile takes approximately
one minute, and adding the proof repeatedly exceeds the 60-second limit.
Local let bindings Yj, X and gj share these expressions. Expanding these bindings
and moving the displayed forall binders back to the parameter list gives the
original type by definitional equality. No mathematical hypothesis or conclusion
changes; no target or underlying definition changes. The binder names of the
inner forall proof hypotheses are prefixed with underscores to avoid the unused
binder linter, and the proof explicitly introduces and uses every hypothesis.
The complete delivered set compiles with this presentation within the limit.

## Old

```lean
theorem perfect_local_models_stage_gluing
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens)
    (hcover : U ⊔ V = ⊤)
    (hU : IsCompact (U : Set (pullback t (Spec.map (R.map (homOfLE hij))) : Scheme.{u})))
    (hV : IsCompact (V : Set (pullback t (Spec.map (R.map (homOfLE hij))) : Scheme.{u})))
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
    (E : schemeDerivedCategory (pullback t (Spec.map (c.ι.app i))))
    (φU : (derivedPullback ((baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app j))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))) ∣_ U)).obj A ≅
      (schemeOpenRestriction _ ((baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app j))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))) ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback ((baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app j))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))) ∣_ V)).obj B ≅
      (schemeOpenRestriction _ ((baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app j))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))) ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      ∃ (F : schemeDerivedCategory
          (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))))
        (a : (derivedPullback g).obj F ⟶ E),
        (∀ x : (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk)))) : Scheme.{u}),
          ∃ W : (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))).Opens,
            x ∈ W ∧ W.toScheme.IsPerfect ((derivedPullback W.ι).obj F)) ∧
        (∀ x : (pullback t (Spec.map (c.ι.app i)) : Scheme.{u}),
          ∃ W : (pullback t (Spec.map (c.ι.app i))).Opens, x ∈ W ∧
            IsIso ((schemeOpenRestriction _ W).mapDerivedCategory.map a))
```

## New

```lean
theorem perfect_local_models_stage_gluing
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (_hcover : U ⊔ V = ⊤)
      (_hU : IsCompact (U : Set Yj)) (_hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (_hA : U.toScheme.IsPerfect A) (_hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X)
      (_φU : (derivedPullback (gj ∣_ U)).obj A ≅
        (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory.obj E)
      (_φV : (derivedPullback (gj ∣_ V)).obj B ≅
        (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      ∃ (F : schemeDerivedCategory
          (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))))
        (a : (derivedPullback g).obj F ⟶ E),
        (∀ x : (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk)))) : Scheme.{u}),
          ∃ W : (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))).Opens,
            x ∈ W ∧ W.toScheme.IsPerfect ((derivedPullback W.ι).obj F)) ∧
        (∀ x : (pullback t (Spec.map (c.ι.app i)) : Scheme.{u}),
          ∃ W : (pullback t (Spec.map (c.ι.app i))).Opens, x ∈ W ∧
            IsIso ((schemeOpenRestriction _ W).mapDerivedCategory.map a))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | claimed (see snapshot lock) | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | claimed (see snapshot lock) | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| TargetsCheck | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | claimed (see snapshot lock) | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | claimed (see snapshot lock) | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed in the clone snapshot | No semantic effect; identical type after let reduction; no adaptation. |

Only PerfectLocalModelsEventuallyCompatible directly applies the declaration
(the other use reported is the declaration itself). All other modules listed are
transitive importers and see the same proposition. Its original source is compiled
against the changed dependency as a compatibility check, without adapting it.
No change to an existing target statement or to definitions used by targets occurs.

## Status

landed 20261013T153459-L-1084958 2026-10-13 (merge of deliver/G2/Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing)
