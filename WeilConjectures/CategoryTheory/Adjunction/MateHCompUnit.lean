/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates along equivalences and mates of pastings

## Main results

- `CategoryTheory.isIso_mateEquiv_symm_of_equivalences`: the inverse mate of an isomorphism of
  squares of right adjoints along equivalences is an isomorphism.
- `CategoryTheory.mateEquiv_app_comp_of_hComp`: the mate of a horizontal pasting of squares is
  the pasting of the mates.
- `CategoryTheory.homEquiv_symm_unit_mateEquiv_symm`: adjuncts of composite units commute with
  the inverse mates of a compatible family of squares of right adjoints.
-/

@[expose] public section

namespace CategoryTheory

/-- Mates of isomorphisms between equivalences are isomorphisms. -/
theorem isIso_mateEquiv_symm_of_equivalences
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'}
    (a : L ⊣ R) (b : L' ⊣ R') [G.IsEquivalence] [H.IsEquivalence]
    (β : TwoSquare R H G R') [IsIso β] :
    IsIso ((mateEquiv a b).symm β) := by
  let eG := G.asEquivalence.toAdjunction
  let eH := H.asEquivalence.toAdjunction
  let α := (mateEquiv a b).symm β
  have hi : IsIso (mateEquiv eH eG β) := by
    have : IsIso eG.unit := inferInstanceAs (IsIso G.asEquivalence.unitIso.hom)
    have : IsIso eH.counit := inferInstanceAs (IsIso H.asEquivalence.counitIso.hom)
    dsimp only [mateEquiv, Equiv.coe_fn_mk]
    infer_instance
  have he := iterated_mateEquiv_conjugateEquiv a b eG eH α
  change (mateEquiv eH eG ((mateEquiv a b) ((mateEquiv a b).symm β))) = _ at he
  rw [Equiv.apply_symm_apply] at he
  have : IsIso (conjugateEquiv (a.comp eH) (eG.comp b) α) := he ▸ hi
  exact conjugateEquiv_of_iso (a.comp eH) (eG.comp b) α


/-- If the square `γ` is the horizontal pasting of `α` and `β` up to the isomorphisms `u` and
`v`, then the mate of `γ` is the pasting of the mates of `α` and `β`, componentwise. -/
theorem mateEquiv_app_comp_of_hComp
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {L₁ : C ⥤ C'} {R₁ : C' ⥤ C} (a₁ : L₁ ⊣ R₁)
    {L₂ : D ⥤ D'} {R₂ : D' ⥤ D} (a₂ : L₂ ⊣ R₂)
    {L₃ : E ⥤ E'} {R₃ : E' ⥤ E} (a₃ : L₃ ⊣ R₃)
    {F : C ⥤ D} {F' : C' ⥤ D'} {G : D ⥤ E} {G' : D' ⥤ E'}
    {H : C ⥤ E} {H' : C' ⥤ E'}
    (α : TwoSquare F L₁ L₂ F') (β : TwoSquare G L₂ L₃ G')
    (γ : TwoSquare H L₁ L₃ H') (u : F ⋙ G ≅ H) (v : F' ⋙ G' ≅ H')
    (ho : ∀ T : C, β.app (F.obj T) ≫ G'.map (α.app T) ≫
      v.hom.app (L₁.obj T) = L₃.map (u.hom.app T) ≫ γ.app T) (K : C') :
    G.map ((mateEquiv a₁ a₂ α).app K) ≫
        (mateEquiv a₂ a₃ β).app (F'.obj K) ≫ R₃.map (v.hom.app K) =
      u.hom.app (R₁.obj K) ≫ (mateEquiv a₁ a₃ γ).app K := by
  have hs : ((TwoSquare.hComp α β).whiskerTop u.inv).whiskerBottom v.hom = γ := by
    ext T
    have ht := congrArg (fun z ↦ L₃.map (u.inv.app T) ≫ z) (ho T)
    simp only [← L₃.map_comp_assoc, Iso.inv_hom_id_app, L₃.map_id,
      Category.id_comp] at ht
    simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using ht
  have hm := mateEquiv_whiskerTop_whiskerBottom a₁ a₃ (TwoSquare.hComp α β)
    u.inv v.hom
  rw [hs, mateEquiv_vcomp a₁ a₂ a₃] at hm
  have hc := congrArg (fun z ↦ z.app K) hm
  apply (cancel_epi (u.inv.app (R₁.obj K))).mp
  change _ = u.inv.app _ ≫ u.hom.app _ ≫ _
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_app_assoc] using hc.symm

/-- Adjuncts of composite units commute with the mates of a compatible family of squares
of right adjoints. -/
theorem homEquiv_symm_unit_mateEquiv_symm
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {L₂ : C₀ ⥤ C₂} {R₂ : C₂ ⥤ C₀} {Rb : C₂ ⥤ C₁}
    {L₁' : D₀ ⥤ D₁} {R₁' : D₁ ⥤ D₀} {L₂' : D₀ ⥤ D₂} {R₂' : D₂ ⥤ D₀} {Rb' : D₂ ⥤ D₁}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (γ : Rb ⋙ R₁ ≅ R₂) (γ' : Rb' ⋙ R₁' ≅ R₂')
    {F₀ : C₀ ⥤ D₀} {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂}
    (σ₁ : R₁ ⋙ F₀ ⟶ F₁ ⋙ R₁') (σ₂ : R₂ ⋙ F₀ ⟶ F₂ ⋙ R₂') (σb : Rb ⋙ F₁ ⟶ F₂ ⋙ Rb')
    (K : C₀)
    (hσ : F₀.map (γ.hom.app (L₂.obj K)) ≫ σ₂.app (L₂.obj K) =
      σ₁.app (Rb.obj (L₂.obj K)) ≫ R₁'.map (σb.app (L₂.obj K)) ≫
        γ'.hom.app (F₂.obj (L₂.obj K))) :
    ((mateEquiv adj₁ adj₁').symm σ₁).app K ≫
        F₁.map ((adj₁.homEquiv _ _).symm (adj₂.unit.app K ≫ γ.inv.app (L₂.obj K))) ≫
        σb.app (L₂.obj K) =
      (adj₁'.homEquiv _ _).symm
          (adj₂'.unit.app (F₀.obj K) ≫ γ'.inv.app (L₂'.obj (F₀.obj K))) ≫
        Rb'.map (((mateEquiv adj₂ adj₂').symm σ₂).app K) := by
  have h₁ := unit_mateEquiv_symm adj₁ adj₁' σ₁ K
  have h₂ := unit_mateEquiv_symm adj₂ adj₂' σ₂ K
  have hT := adj₁.homEquiv_unit K _ ((adj₁.homEquiv _ _).symm
    (adj₂.unit.app K ≫ γ.inv.app (L₂.obj K)))
  rw [Equiv.apply_symm_apply] at hT
  have hT' := adj₁'.homEquiv_unit (F₀.obj K) _ ((adj₁'.homEquiv _ _).symm
    (adj₂'.unit.app (F₀.obj K) ≫ γ'.inv.app (L₂'.obj (F₀.obj K))))
  rw [Equiv.apply_symm_apply] at hT'
  have hn := σ₁.naturality
    ((adj₁.homEquiv _ _).symm (adj₂.unit.app K ≫ γ.inv.app (L₂.obj K)))
  have hγ := γ'.inv.naturality (((mateEquiv adj₂ adj₂').symm σ₂).app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h₁ h₂ hn hT hT' hγ ⊢
  apply (adj₁'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [← h₁]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← F₀.map_comp_assoc, ← hT, ← reassoc_of% hT', ← hγ,
    ← reassoc_of% h₂, F₀.map_comp_assoc]
  congr 1
  rw [← cancel_epi (F₀.map (γ.hom.app (L₂.obj K))), ← F₀.map_comp_assoc,
    Iso.hom_inv_id_app, F₀.map_id, Category.id_comp, reassoc_of% hσ, Iso.hom_inv_id_app]
  simp

end CategoryTheory
