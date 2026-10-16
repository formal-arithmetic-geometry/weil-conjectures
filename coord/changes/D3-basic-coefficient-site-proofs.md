# Proofs of the Basic coefficient-site instances

## Reason

The refreshed source baseline has eight holes. Reuse the complete proofs already present in
the first shared-source snapshot. Seven are existing proposition-valued instances, whose
proof-body replacements the delivery checker classifies as interface changes. Proof irrelevance
preserves their values; all existing signatures, universes, visibility and public imports stay
identical. The new private helpers prove the affine-spectrum Hom correspondence and naturality;
they occur only in proofs of propositions. No data definition, target statement, coefficient
morphism or consumer is changed. The target definition review therefore does not reopen.

## Old

```lean
instance AddCommGrpCat.hasFunctorialFlatResolution :
    Abelian.HasFunctorialFlatResolution Ab.{u} :=
  sorry
```

```lean
instance weaklyEtale_toSpecZ_profiniteToScheme (S : Profinite.{u}) :
    WeaklyEtale (toSpecZ (profiniteToScheme.obj S)) :=
  sorry
```

```lean
instance preservesFiniteLimits_profiniteToProEt : PreservesFiniteLimits profiniteToProEt.{u} :=
  sorry
```

```lean
lemma coverPreserving_profiniteToProEt :
    CoverPreserving (coherentTopology Profinite.{u}) (ProEt.topology specZ) profiniteToProEt :=
  sorry
```

```lean
instance hasLeftKanExtension_op_profiniteToProEt (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :
    profiniteToProEt.op.HasLeftKanExtension F :=
  sorry
```

```lean
instance isIso_η_pointUpperStar : IsIso (η pointUpperStar.{u}) :=
  sorry
```

```lean
instance isIso_δ_pointUpperStar (F G : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    IsIso (δ pointUpperStar F G) :=
  sorry
```

```lean
instance isMonoidal_upperStarFromPointComp :
    NatTrans.IsMonoidal (upperStarFromPointComp f).hom :=
  sorry
```

## New

```lean
instance AddCommGrpCat.hasFunctorialFlatResolution :
    Abelian.HasFunctorialFlatResolution Ab.{u} := by
  infer_instance
```

```lean
instance weaklyEtale_toSpecZ_profiniteToScheme (S : Profinite.{u}) :
    WeaklyEtale (toSpecZ (profiniteToScheme.obj S)) := by
  let e : CommRingCat.of (LocallyConstant S (ULift.{u} ℤ)) ≅
      CommRingCat.of (LocallyConstant S ℤ) :=
    (LocallyConstant.congrRightRingEquiv ULift.ringEquiv).toCommRingCatIso
  have : WeaklyEtale
      (Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (ULift.{u} ℤ) (LocallyConstant S (ULift.{u} ℤ))))) := by
    infer_instance
  rwa [specULiftZIsTerminal.hom_ext
    (Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (LocallyConstant S (ULift.{u} ℤ)))))
    (toSpecZ (profiniteToScheme.obj S))] at this
```

```lean
instance preservesFiniteLimits_profiniteToProEt : PreservesFiniteLimits profiniteToProEt.{u} := by
  have h := (Adjunction.adjunctionOfEquivLeft profiniteLocallyConstantHomEquiv
    profiniteLocallyConstantHomEquiv_naturality).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits profiniteToCommRingCatOp.{u} := inferInstance
  have : PreservesFiniteLimits profiniteToScheme.{u} := by
    unfold profiniteToScheme
    infer_instance
  have : (Over.forget specZ.{u}).IsEquivalence :=
    (Over.equivalenceOfIsTerminal specULiftZIsTerminal).isEquivalence_functor
  have : PreservesFiniteLimits
      ((profiniteToProEt.{u} ⋙ Scheme.ProEt.forget specZ) ⋙ Over.forget specZ) :=
    inferInstanceAs (PreservesFiniteLimits profiniteToScheme.{u})
  have : PreservesFiniteLimits (profiniteToProEt.{u} ⋙ Scheme.ProEt.forget specZ) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (Over.forget specZ)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Scheme.ProEt.forget specZ)
```

```lean
lemma coverPreserving_profiniteToProEt :
    CoverPreserving (coherentTopology Profinite.{u}) (ProEt.topology specZ) profiniteToProEt := by
  classical
  constructor
  intro T R hR
  obtain ⟨ι, hι, S, f, hf, hRf⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily R).mp hR
  have hsurj := ((Profinite.effectiveEpiFamily_tfae S f).out 0 2).mp hf
  have hgeom : ∀ q : profiniteToScheme.obj T,
      ∃ i, q ∈ Set.range (profiniteToScheme.map (f i)) := by
    intro q
    obtain ⟨⟨t, p⟩, rfl⟩ := LocallyConstant.toPrimeSpectrum_surjective q
    obtain ⟨i, s, hs⟩ := hsurj t
    refine ⟨i, LocallyConstant.toPrimeSpectrum (s, p), ?_⟩
    subst t
    rfl
  have hwe (i : ι) : WeaklyEtale (profiniteToScheme.map (f i)) := by
    have : WeaklyEtale (profiniteToScheme.map (f i) ≫
        toSpecZ (profiniteToScheme.obj T)) := by
      rw [comp_toSpecZ]
      infer_instance
    exact WeaklyEtale.of_comp _ (toSpecZ (profiniteToScheme.obj T))
  let C := Scheme.Cover.mkOfCovers (P := @WeaklyEtale) ι
    (fun i ↦ profiniteToScheme.obj (S i)) (fun i ↦ profiniteToScheme.map (f i))
    hgeom hwe
  have (i : C.I₀) : QuasiCompact (C.f i) := by
    change QuasiCompact (Spec.map _)
    infer_instance
  have : Finite C.I₀ := hι
  have hcov : Presieve.ofArrows (fun i ↦ profiniteToProEt.obj (S i))
      (fun i ↦ profiniteToProEt.map (f i)) ∈ ProEt.precoverage specZ (profiniteToProEt.obj T) := by
    rw [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact (Scheme.Cover.ofQuasiCompactCover C).mem₀
  apply (ProEt.topology specZ).superset_covering _
    (Precoverage.generate_mem_toGrothendieck hcov)
  rw [Sieve.generate_le_iff]
  intro W g hg
  obtain ⟨i⟩ := hg
  exact R.image_mem_functorPushforward profiniteToProEt (hRf i)
```

```lean
instance hasLeftKanExtension_op_profiniteToProEt (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :
    profiniteToProEt.op.HasLeftKanExtension F := by
  infer_instance
```

```lean
instance isIso_η_pointUpperStar : IsIso (η pointUpperStar.{u}) := by
  unfold pointUpperStar
  infer_instance
```

```lean
instance isIso_δ_pointUpperStar (F G : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    IsIso (δ pointUpperStar F G) := by
  unfold pointUpperStar
  infer_instance
```

```lean
instance isMonoidal_upperStarFromPointComp :
    NatTrans.IsMonoidal (upperStarFromPointComp f).hom := by
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ toSpecZ Y))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y)).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} f))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact Adjunction.isMonoidal_comp _ _
  have hr : NatTrans.IsMonoidal (lowerStarComp Ab.{u + 1} f (toSpecZ Y)).hom := by
    unfold lowerStarComp
    infer_instance
  have hc : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f (toSpecZ Y)).inv :=
    isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp Ab.{u + 1} f (toSpecZ Y)).inv
  have he (g g' : X ⟶ specZ.{u}) (h : g = g') : NatTrans.IsMonoidal
      (eqToIso (congrArg (upperStar Ab.{u + 1}) h)).hom := by
    subst g'
    exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))
  have := he (f ≫ toSpecZ Y) (toSpecZ X) (comp_toSpecZ f)
  unfold upperStarFromPointComp
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  infer_instance
```

The accompanying private helper construction is exactly the already recorded
AlgebraicGeometry.ProEtale.profiniteLocallyConstantHomEquiv of
`def-weil-pbc-profinite-locally-constant-hom-equiv`, together with its proved localization
and naturality lemmas. All five additional imports are proof-only ordinary imports.

## Users

Every transitive consumer reported by tools/downstream.py is listed here, with the holder
recorded when this report was prepared. None requires adaptation: the public API is unchanged
and the only changed instance bodies inhabit propositions. In particular, the old coefficient
morphism definitions are kept verbatim. No target changes mathematical meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexCompatibility | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisPushforward | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisUnit | C2 | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | B2 | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ComapUpperStarIsoComposition | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ComapUpperStarIsoMate | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedCoefficientFamilyHomStage | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedCoefficientHomStage | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedCoefficientPointUnitPasting | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedConstructibleGenericLfp | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedConstructiblePiece | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | C1 | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFiniteFreeDerivedHom | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFiniteFreeHomContinuity | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFiniteFreeHomEvaluation | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFiniteFreeInternalHomColimits | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFiniteFreeTensorExact | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelImmersionRestriction | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationMatrices | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedFpHomStage | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedHypercoverComparison | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedHypercoverInjectiveRow | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedInternalHomSections | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedLocalCoefficientAdjoints | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedLocalPresentationPullback | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedPiece | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedPointBasisEvaluation | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpCoverComposition | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | E1 | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedQcqsPushforwardLocalComparison | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedSurjectiveClosedEquivalence | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedSurjectiveClosedLocalPresentation | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.CondensedUnderivedPushforwardContinuity | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralCoefficientTelescope | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralCoefficients | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralDerivedUnit | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralScalarExact | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersection | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | E4 | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | F1 | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSections | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | B3 | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientTerminal | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteDiscreteSchemeRing | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | F2 | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.GeometricFieldProEtaleEvaluation | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.GeometricFieldProfiniteDenseSubsite | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralReductionScalar | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralReductionTensor | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralReductionTriangulatedProperty | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueComparisonInterface | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueDerivedMonoidal | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueOrdinaryMonoidal | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueOrdinaryRestrictPullComp | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResiduePerfect | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResiduePullFlatModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResiduePullOrdinaryUnit | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResiduePullSquare | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResiduePullSquareComp | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResiduePullSquareData | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResiduePullSquareIsIso | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResiduePullbackPreservesFlat | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueRestrictPullComp | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | A2 | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorPresentation | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | B4 | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.InverseImageModuleFlat | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ModuleObjectFreeGenerators | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.PointLanAffineEvaluation | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.PointLanFiniteProducts | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ProEtalePointComponentsMaps | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ProEtaleSheafificationWcontractibleSections | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ProfinitePointPullback | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.ProfiniteTestObjectFunctor | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.SectionModuleAlgebraicInverseImage | C3 | Same signatures and proposition instances; no adaptation. |
| Sheaf.Paper.SplitProEtaleModuleProductMap | unclaimed | Same signatures and proposition instances; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same signatures and proposition instances; no adaptation. |
| TargetsCheck | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic | D3 | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | D2 | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | A4 | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal | D4 | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | G2 | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | G1 | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.TateTwist.ProEtale | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.TraceFormula.Main | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Same signatures and proposition instances; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Same signatures and proposition instances; no adaptation. |

## Status

landed 20261016T221604-L-1612926 2026-10-16 (merge of deliver/D3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic)
