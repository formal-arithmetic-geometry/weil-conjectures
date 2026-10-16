# CategoryTheory.Mod.tensorPresentationDerivedCounit

## Reason

The return identifies the copied residueTensorHom_linear as word-for-word identical
to the existing extendTensorHom_linear. The canonical tensor presentation used by
normalization needs concrete data, so an existential choice of a presentation is
insufficient. Expose the existing proved helper chain in its original, unclaimed
module and import it; remove every copied helper and counit from the new module.
Only visibility changes: all types, bodies, universes and hypotheses stay identical.
No target definition or statement changes meaning. The generic tensor instance in
the new module is for arbitrary C, rather than only Mod C R.

## Old

```lean
omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma extendTensorHom_linear :
    γ[R,((comap φ).obj ((extendScalars φ).obj M)).X] ≫
        (extendForgetTensorObjIso φ M).hom =
      R ◁ (extendForgetTensorObjIso φ M).hom ≫
        γ[R,(((comap φ).obj (regular S)) ⊗ M).X] := by
  apply (cancel_epi (R ◁ extendπ φ M)).1
  change R ◁ extendπ φ M ≫ (φ ▷ (extendScalarsObj φ M).X ≫
      γ[S,(extendScalarsObj φ M).X]) ≫ (extendForgetTensorObjIso φ M).hom = _
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, whiskerLeft_extendπ_smul_assoc]
  have hπ : extendπ φ M ≫ (extendForgetTensorObjIso φ M).hom =
      tensorObjπ ((comap φ).obj (regular S)) M := by
    simp only [extendForgetTensorObjIso, extendπ_extendDescHom]
  rw [hπ, ← whiskerLeft_comp_assoc, hπ, whiskerLeft_tensorπ_smul]
  change φ ▷ (S ⊗ M.X) ≫ (α_ S S M.X).inv ≫ μ[S] ▷ M.X ≫ _ =
    (α_ R S M.X).inv ≫ (φ ▷ S ≫ μ[S]) ▷ M.X ≫ _
  rw [associator_inv_naturality_left_assoc, comp_whiskerRight, Category.assoc]

private noncomputable def extendComapTensorIso :
    extendScalars φ ⋙ comap φ ≅ tensorLeft ((comap φ).obj (regular S)) :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk (extendForgetTensorObjIso φ M) (extendTensorHom_linear φ M))
    (by
      intro M N f
      apply (forget R).map_injective
      exact (extendForgetTensorIso φ).hom.naturality f)

private noncomputable def extendComapCounit :
    DerivedCategory.Qh ⋙ ((extendScalars φ).leftDerivedFunctor ⋙
        (comap φ).mapDerivedCategory) ⟶
      (extendScalars φ ⋙ comap φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (extendScalars φ).leftDerivedFunctorCounit
      (comap φ).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((extendScalars φ).mapHomotopyCategory (.up ℤ))
      (comap φ).mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (extendScalars φ ⋙ comap φ)) (.up ℤ)).hom
      DerivedCategory.Qh

private instance tensorLeft_preservesKFlatQuasiIso (B : Mod C R) :
    (tensorLeft B).PreservesKFlatQuasiIso := by
  refine Functor.PreservesKFlatQuasiIso.mk' _ ?_
  intro K hK hKa
  exact (CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa B).of_iso
    ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight B) _).app K).symm

private noncomputable def tensorPresentationHomotopyIso :
    (extendScalars φ ⋙ comap φ).mapHomotopyCategory (.up ℤ) ≅
      (tensorLeft ((comap φ).obj (regular S))).mapHomotopyCategory (.up ℤ) :=
  let e := extendComapTensorIso φ
  { hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
    inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
    hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
    inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }

private noncomputable def tensorPresentationDerivedCounit :
    DerivedCategory.Qh ⋙ ((extendScalars φ).leftDerivedFunctor ⋙
        (comap φ).mapDerivedCategory) ⟶
      (tensorLeft ((comap φ).obj (regular S))).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  extendComapCounit φ ≫
    Functor.whiskerRight (tensorPresentationHomotopyIso φ).hom DerivedCategory.Qh

private lemma tensorPresentationDerivedCounit_isLeftDerivedFunctor :
    ((extendScalars φ).leftDerivedFunctor ⋙ (comap φ).mapDerivedCategory).IsLeftDerivedFunctor
      (tensorPresentationDerivedCounit φ) (HomotopyCategory.quasiIso (Mod C R) (.up ℤ)) := by
  apply ((tensorLeft ((comap φ).obj (regular S))).isLeftDerivedFunctor_iff_isIso_app_of_kFlat
    (tensorPresentationDerivedCounit φ)).2
  intro K hK
  have := (extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat K hK
  dsimp only [tensorPresentationDerivedCounit, extendComapCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

```

## New

```lean
omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
lemma extendTensorHom_linear :
    γ[R,((comap φ).obj ((extendScalars φ).obj M)).X] ≫
        (extendForgetTensorObjIso φ M).hom =
      R ◁ (extendForgetTensorObjIso φ M).hom ≫
        γ[R,(((comap φ).obj (regular S)) ⊗ M).X] := by
  apply (cancel_epi (R ◁ extendπ φ M)).1
  change R ◁ extendπ φ M ≫ (φ ▷ (extendScalarsObj φ M).X ≫
      γ[S,(extendScalarsObj φ M).X]) ≫ (extendForgetTensorObjIso φ M).hom = _
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, whiskerLeft_extendπ_smul_assoc]
  have hπ : extendπ φ M ≫ (extendForgetTensorObjIso φ M).hom =
      tensorObjπ ((comap φ).obj (regular S)) M := by
    simp only [extendForgetTensorObjIso, extendπ_extendDescHom]
  rw [hπ, ← whiskerLeft_comp_assoc, hπ, whiskerLeft_tensorπ_smul]
  change φ ▷ (S ⊗ M.X) ≫ (α_ S S M.X).inv ≫ μ[S] ▷ M.X ≫ _ =
    (α_ R S M.X).inv ≫ (φ ▷ S ≫ μ[S]) ▷ M.X ≫ _
  rw [associator_inv_naturality_left_assoc, comp_whiskerRight, Category.assoc]

noncomputable def extendComapTensorIso :
    extendScalars φ ⋙ comap φ ≅ tensorLeft ((comap φ).obj (regular S)) :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk (extendForgetTensorObjIso φ M) (extendTensorHom_linear φ M))
    (by
      intro M N f
      apply (forget R).map_injective
      exact (extendForgetTensorIso φ).hom.naturality f)

noncomputable def extendComapCounit :
    DerivedCategory.Qh ⋙ ((extendScalars φ).leftDerivedFunctor ⋙
        (comap φ).mapDerivedCategory) ⟶
      (extendScalars φ ⋙ comap φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (extendScalars φ).leftDerivedFunctorCounit
      (comap φ).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((extendScalars φ).mapHomotopyCategory (.up ℤ))
      (comap φ).mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (extendScalars φ ⋙ comap φ)) (.up ℤ)).hom
      DerivedCategory.Qh

instance tensorLeft_preservesKFlatQuasiIso (B : Mod C R) :
    (tensorLeft B).PreservesKFlatQuasiIso := by
  refine Functor.PreservesKFlatQuasiIso.mk' _ ?_
  intro K hK hKa
  exact (CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa B).of_iso
    ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight B) _).app K).symm

noncomputable def tensorPresentationHomotopyIso :
    (extendScalars φ ⋙ comap φ).mapHomotopyCategory (.up ℤ) ≅
      (tensorLeft ((comap φ).obj (regular S))).mapHomotopyCategory (.up ℤ) :=
  let e := extendComapTensorIso φ
  { hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
    inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
    hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
    inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }

noncomputable def tensorPresentationDerivedCounit :
    DerivedCategory.Qh ⋙ ((extendScalars φ).leftDerivedFunctor ⋙
        (comap φ).mapDerivedCategory) ⟶
      (tensorLeft ((comap φ).obj (regular S))).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  extendComapCounit φ ≫
    Functor.whiskerRight (tensorPresentationHomotopyIso φ).hom DerivedCategory.Qh

lemma tensorPresentationDerivedCounit_isLeftDerivedFunctor :
    ((extendScalars φ).leftDerivedFunctor ⋙ (comap φ).mapDerivedCategory).IsLeftDerivedFunctor
      (tensorPresentationDerivedCounit φ) (HomotopyCategory.quasiIso (Mod C R) (.up ℤ)) := by
  apply ((tensorLeft ((comap φ).obj (regular S))).isLeftDerivedFunctor_iff_isIso_app_of_kFlat
    (tensorPresentationDerivedCounit φ)).2
  intro K hK
  have := (extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat K hK
  dsimp only [tensorPresentationDerivedCounit, extendComapCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

```

## Users

`tools/downstream.py Sheaf.Paper.IntegralReductionTensor --uses tensorPresentationDerivedCounit`
lists only the original module as a name user, and eight downstream modules.
The full list is below. Existing consumers require no adaptations because the
existing public theorem type and proof body are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralReductionTensor | unclaimed | Expose existing helpers; no proof or type change. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No source change; exported theorem unchanged. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No source change; exported theorem unchanged. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No source change; exported theorem unchanged. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No source change; exported theorem unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No source change; exported theorem unchanged. |
| TargetsCheck | unclaimed | No source change; exported theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No source change; exported theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No source change; exported theorem unchanged. |
| Sheaf.Paper.IntegralResidueTensorPresentation | D3 | Import and use the existing canonical counit API; remove copies. |

## Status

landed 20261016T101204-L-2230257 2026-10-16 (merge of deliver/D3/Sheaf.Paper.IntegralResidueProjectionNormalization)
