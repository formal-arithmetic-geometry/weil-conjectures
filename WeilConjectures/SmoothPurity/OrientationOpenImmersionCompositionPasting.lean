/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Pasting exchange morphisms along a composite with a unit identification

An abstract pasting lemma used to compare the coefficient comparisons of the relative
dualizing complexes `Rf^! 𝟙` along a composite `f ≫ j`
(`CategoryTheory.map_map_comp_comp_exchange_eq`).

Three "exceptional inverse image" functors `R_f`, `R_j`, `R_{f ≫ j}` are given on three levels
`0, 1, 2` of coefficients, with change of coefficients functors `S : 0 → 1` and `T : 1 → 2`,
exchange morphisms `β : R ⋙ S ⟶ S ⋙ R`, `γ : R ⋙ T ⟶ T ⋙ R` and comparison morphisms
`c : R_j ⋙ R_f ⟶ R_{f ≫ j}`. If the exchange morphisms are compatible with the comparisons, and
if the comparison of `R_j` at the unit is compatible with given unit identifications, then the
comparisons of `R_f` and `R_{f ≫ j}` at the units are compatible with the comparisons
`c` and the unit identifications.
-/

@[expose] public section

namespace CategoryTheory

/-- **Pasting the exchange morphisms along a composite.** Let `R_f, R_j, R_{fj}` be functors on
three levels of coefficients `0, 1, 2`, with change of coefficients `S : 0 → 1`, `T : 1 → 2`,
exchange morphisms `β : R ⋙ S ⟶ S ⋙ R`, `γ : R ⋙ T ⟶ T ⋙ R` and comparisons
`c : R_j ⋙ R_f ⟶ R_{fj}` such that the exchange morphisms of `f ≫ j` are those of `f` and `j`
pasted along `c` (`h₁`, `h₂`). Given objects `Y_i`, `Z_i` (the units) with identifications
`e : S Y₀ ⟶ Y₁`, ... and morphisms `u : Y_i ⟶ R_j Z_i` such that the comparison
`T S R_j Z₀ ⟶ R_j Z₂` of `j` carries `u₀` to `u₂` (`hj`), the comparisons
`T S R_f Y₀ ⟶ R_f Y₂` and `T S R_{fj} Z₀ ⟶ R_{fj} Z₂` are compatible with
`R_f u ≫ c`. -/
lemma map_map_comp_comp_exchange_eq {CX₀ CY₀ CZ₀ CX₁ CY₁ CZ₁ CX₂ CY₂ CZ₂ : Type*}
    [Category* CX₀] [Category* CY₀] [Category* CZ₀] [Category* CX₁] [Category* CY₁]
    [Category* CZ₁] [Category* CX₂] [Category* CY₂] [Category* CZ₂]
    {Rf₀ : CY₀ ⥤ CX₀} {Rj₀ : CZ₀ ⥤ CY₀} {Rfj₀ : CZ₀ ⥤ CX₀}
    {Rf₁ : CY₁ ⥤ CX₁} {Rj₁ : CZ₁ ⥤ CY₁} {Rfj₁ : CZ₁ ⥤ CX₁}
    {Rf₂ : CY₂ ⥤ CX₂} {Rj₂ : CZ₂ ⥤ CY₂} {Rfj₂ : CZ₂ ⥤ CX₂}
    {SX : CX₀ ⥤ CX₁} {SY : CY₀ ⥤ CY₁} {SZ : CZ₀ ⥤ CZ₁}
    {TX : CX₁ ⥤ CX₂} {TY : CY₁ ⥤ CY₂} {TZ : CZ₁ ⥤ CZ₂}
    (βf : Rf₀ ⋙ SX ⟶ SY ⋙ Rf₁) (βj : Rj₀ ⋙ SY ⟶ SZ ⋙ Rj₁) (βfj : Rfj₀ ⋙ SX ⟶ SZ ⋙ Rfj₁)
    (γf : Rf₁ ⋙ TX ⟶ TY ⋙ Rf₂) (γj : Rj₁ ⋙ TY ⟶ TZ ⋙ Rj₂) (γfj : Rfj₁ ⋙ TX ⟶ TZ ⋙ Rfj₂)
    (c₀ : Rj₀ ⋙ Rf₀ ⟶ Rfj₀) (c₁ : Rj₁ ⋙ Rf₁ ⟶ Rfj₁) (c₂ : Rj₂ ⋙ Rf₂ ⟶ Rfj₂)
    {Y₀ : CY₀} {Z₀ : CZ₀} {Y₁ : CY₁} {Z₁ : CZ₁} {Y₂ : CY₂} {Z₂ : CZ₂}
    (u₀ : Y₀ ⟶ Rj₀.obj Z₀) (u₂ : Y₂ ⟶ Rj₂.obj Z₂)
    (eY₁ : SY.obj Y₀ ⟶ Y₁) (eZ₁ : SZ.obj Z₀ ⟶ Z₁) (eY₂ : TY.obj Y₁ ⟶ Y₂) (eZ₂ : TZ.obj Z₁ ⟶ Z₂)
    (h₁ : SX.map (c₀.app Z₀) ≫ βfj.app Z₀ =
      βf.app (Rj₀.obj Z₀) ≫ Rf₁.map (βj.app Z₀) ≫ c₁.app (SZ.obj Z₀))
    (h₂ : TX.map (c₁.app Z₁) ≫ γfj.app Z₁ =
      γf.app (Rj₁.obj Z₁) ≫ Rf₂.map (γj.app Z₁) ≫ c₂.app (TZ.obj Z₁))
    (hj : TY.map (SY.map u₀) ≫ TY.map (βj.app Z₀ ≫ Rj₁.map eZ₁) ≫ γj.app Z₁ ≫ Rj₂.map eZ₂ =
      TY.map eY₁ ≫ eY₂ ≫ u₂) :
    TX.map (SX.map (Rf₀.map u₀ ≫ c₀.app Z₀)) ≫
        (TX.map (βfj.app Z₀ ≫ Rfj₁.map eZ₁) ≫ γfj.app Z₁ ≫ Rfj₂.map eZ₂) =
      (TX.map (βf.app Y₀ ≫ Rf₁.map eY₁) ≫ γf.app Y₁ ≫ Rf₂.map eY₂) ≫ Rf₂.map u₂ ≫ c₂.app Z₂ := by
  have nβf := βf.naturality u₀
  have nc₁ := c₁.naturality eZ₁
  have nc₂ := c₂.naturality eZ₂
  have nγf := γf.naturality (SY.map u₀ ≫ βj.app Z₀ ≫ Rj₁.map eZ₁)
  have nγf' := γf.naturality eY₁
  simp only [Functor.comp_obj, Functor.comp_map] at nβf nc₁ nc₂ nγf nγf'
  calc _ = TX.map (SX.map (Rf₀.map u₀) ≫ (SX.map (c₀.app Z₀) ≫ βfj.app Z₀) ≫
        Rfj₁.map eZ₁) ≫ γfj.app Z₁ ≫ Rfj₂.map eZ₂ := by simp
    _ = TX.map (βf.app Y₀ ≫ Rf₁.map (SY.map u₀ ≫ βj.app Z₀ ≫ Rj₁.map eZ₁)) ≫
        (TX.map (c₁.app Z₁) ≫ γfj.app Z₁) ≫ Rfj₂.map eZ₂ := by
      rw [h₁]
      simp only [Category.assoc, ← nc₁, reassoc_of% nβf, Functor.map_comp]
    _ = TX.map (βf.app Y₀) ≫ (TX.map (Rf₁.map (SY.map u₀ ≫ βj.app Z₀ ≫ Rj₁.map eZ₁)) ≫
        γf.app (Rj₁.obj Z₁)) ≫ Rf₂.map (γj.app Z₁) ≫ Rf₂.map (Rj₂.map eZ₂) ≫ c₂.app Z₂ := by
      rw [h₂]
      simp only [Category.assoc, nc₂, Functor.map_comp]
    _ = TX.map (βf.app Y₀) ≫ γf.app (SY.obj Y₀) ≫
        Rf₂.map (TY.map (SY.map u₀) ≫ TY.map (βj.app Z₀ ≫ Rj₁.map eZ₁) ≫ γj.app Z₁ ≫
          Rj₂.map eZ₂) ≫ c₂.app Z₂ := by
      rw [nγf]
      simp
    _ = _ := by
      rw [hj, Functor.map_comp, Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc, reassoc_of% nγf']

/-- `CategoryTheory.map_map_comp_comp_exchange_eq` with the three comparisons at the units given
as morphisms `cf`, `cj`, `cfj` together with their expressions. -/
lemma map_map_comp_comp_exchange_eq' {CX₀ CY₀ CZ₀ CX₁ CY₁ CZ₁ CX₂ CY₂ CZ₂ : Type*}
    [Category* CX₀] [Category* CY₀] [Category* CZ₀] [Category* CX₁] [Category* CY₁]
    [Category* CZ₁] [Category* CX₂] [Category* CY₂] [Category* CZ₂]
    {Rf₀ : CY₀ ⥤ CX₀} {Rj₀ : CZ₀ ⥤ CY₀} {Rfj₀ : CZ₀ ⥤ CX₀}
    {Rf₁ : CY₁ ⥤ CX₁} {Rj₁ : CZ₁ ⥤ CY₁} {Rfj₁ : CZ₁ ⥤ CX₁}
    {Rf₂ : CY₂ ⥤ CX₂} {Rj₂ : CZ₂ ⥤ CY₂} {Rfj₂ : CZ₂ ⥤ CX₂}
    {SX : CX₀ ⥤ CX₁} {SY : CY₀ ⥤ CY₁} {SZ : CZ₀ ⥤ CZ₁}
    {TX : CX₁ ⥤ CX₂} {TY : CY₁ ⥤ CY₂} {TZ : CZ₁ ⥤ CZ₂}
    (βf : Rf₀ ⋙ SX ⟶ SY ⋙ Rf₁) (βj : Rj₀ ⋙ SY ⟶ SZ ⋙ Rj₁) (βfj : Rfj₀ ⋙ SX ⟶ SZ ⋙ Rfj₁)
    (γf : Rf₁ ⋙ TX ⟶ TY ⋙ Rf₂) (γj : Rj₁ ⋙ TY ⟶ TZ ⋙ Rj₂) (γfj : Rfj₁ ⋙ TX ⟶ TZ ⋙ Rfj₂)
    (c₀ : Rj₀ ⋙ Rf₀ ⟶ Rfj₀) (c₁ : Rj₁ ⋙ Rf₁ ⟶ Rfj₁) (c₂ : Rj₂ ⋙ Rf₂ ⟶ Rfj₂)
    {Y₀ : CY₀} {Z₀ : CZ₀} {Y₁ : CY₁} {Z₁ : CZ₁} {Y₂ : CY₂} {Z₂ : CZ₂}
    (u₀ : Y₀ ⟶ Rj₀.obj Z₀) (u₂ : Y₂ ⟶ Rj₂.obj Z₂)
    (eY₁ : SY.obj Y₀ ⟶ Y₁) (eZ₁ : SZ.obj Z₀ ⟶ Z₁) (eY₂ : TY.obj Y₁ ⟶ Y₂) (eZ₂ : TZ.obj Z₁ ⟶ Z₂)
    (cf : TX.obj (SX.obj (Rf₀.obj Y₀)) ⟶ Rf₂.obj Y₂)
    (cj : TY.obj (SY.obj (Rj₀.obj Z₀)) ⟶ Rj₂.obj Z₂)
    (cfj : TX.obj (SX.obj (Rfj₀.obj Z₀)) ⟶ Rfj₂.obj Z₂)
    (hcf : cf = TX.map (βf.app Y₀ ≫ Rf₁.map eY₁) ≫ γf.app Y₁ ≫ Rf₂.map eY₂)
    (hcj : cj = TY.map (βj.app Z₀ ≫ Rj₁.map eZ₁) ≫ γj.app Z₁ ≫ Rj₂.map eZ₂)
    (hcfj : cfj = TX.map (βfj.app Z₀ ≫ Rfj₁.map eZ₁) ≫ γfj.app Z₁ ≫ Rfj₂.map eZ₂)
    (h₁ : SX.map (c₀.app Z₀) ≫ βfj.app Z₀ =
      βf.app (Rj₀.obj Z₀) ≫ Rf₁.map (βj.app Z₀) ≫ c₁.app (SZ.obj Z₀))
    (h₂ : TX.map (c₁.app Z₁) ≫ γfj.app Z₁ =
      γf.app (Rj₁.obj Z₁) ≫ Rf₂.map (γj.app Z₁) ≫ c₂.app (TZ.obj Z₁))
    (hj : TY.map (SY.map u₀) ≫ cj = TY.map eY₁ ≫ eY₂ ≫ u₂) :
    TX.map (SX.map (Rf₀.map u₀ ≫ c₀.app Z₀)) ≫ cfj = cf ≫ Rf₂.map u₂ ≫ c₂.app Z₂ := by
  subst hcf hcj hcfj
  exact map_map_comp_comp_exchange_eq βf βj βfj γf γj γfj c₀ c₁ c₂ u₀ u₂ eY₁ eZ₁ eY₂ eZ₂ h₁ h₂ hj

section Mates

variable {C₁ C₂ C₃ C₁' C₂' C₃' : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₁'] [Category* C₂'] [Category* C₃']
  {L₁₂ : C₁ ⥤ C₂} {R₂₁ : C₂ ⥤ C₁} {L₂₃ : C₂ ⥤ C₃} {R₃₂ : C₃ ⥤ C₂}
  {L₁₃ : C₁ ⥤ C₃} {R₃₁ : C₃ ⥤ C₁}
  {L₁₂' : C₁' ⥤ C₂'} {R₂₁' : C₂' ⥤ C₁'} {L₂₃' : C₂' ⥤ C₃'} {R₃₂' : C₃' ⥤ C₂'}
  {L₁₃' : C₁' ⥤ C₃'} {R₃₁' : C₃' ⥤ C₁'}
  (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂) (adj₁₃ : L₁₃ ⊣ R₃₁)
  (adj₁₂' : L₁₂' ⊣ R₂₁') (adj₂₃' : L₂₃' ⊣ R₃₂') (adj₁₃' : L₁₃' ⊣ R₃₁')
  {T₁ : C₁ ⥤ C₁'} {T₂ : C₂ ⥤ C₂'} {T₃ : C₃ ⥤ C₃'}
  (e₁₂ : L₁₂ ⋙ T₂ ≅ T₁ ⋙ L₁₂') (e₂₃ : L₂₃ ⋙ T₃ ≅ T₂ ⋙ L₂₃') (e₁₃ : L₁₃ ⋙ T₃ ≅ T₁ ⋙ L₁₃')
  (c : L₁₃ ≅ L₁₂ ⋙ L₂₃) (c' : L₁₃' ≅ L₁₂' ⋙ L₂₃')

/-- **Mates of compatible isomorphisms are compatible with the conjugate composition
isomorphisms.** (A copy of `CategoryTheory.mateEquiv_conjugateIsoEquiv_comp_app`, whose file has
heavy imports.) Let `e_{ij} : L_{ij} ⋙ T_j ≅ T_i ⋙ L'_{ij}` be isomorphisms compatible with
composition isomorphisms `c : L₁₃ ≅ L₁₂ ⋙ L₂₃` and `c'`. Then the mates
`β_{ij} : R_{ji} ⋙ T_i ⟶ T_j ⋙ R'_{ji}` of the inverses of `e_{ij}` are compatible with the
conjugates `R₃₂ ⋙ R₂₁ ≅ R₃₁` of `c` and `c'`. -/
lemma exchange_conjugateIsoEquiv_comp_app
    (h : ∀ M, e₁₃.hom.app M ≫ c'.hom.app (T₁.obj M) =
      T₃.map (c.hom.app M) ≫ e₂₃.hom.app (L₁₂.obj M) ≫ L₂₃'.map (e₁₂.hom.app M))
    (N : C₃) :
    T₁.map ((conjugateIsoEquiv (adj₁₂.comp adj₂₃) adj₁₃ c).hom.app N) ≫
        (mateEquiv adj₁₃ adj₁₃' (.mk _ _ _ _ e₁₃.inv)).natTrans.app N =
      (mateEquiv adj₁₂ adj₁₂' (.mk _ _ _ _ e₁₂.inv)).natTrans.app (R₃₂.obj N) ≫
        R₂₁'.map ((mateEquiv adj₂₃ adj₂₃' (.mk _ _ _ _ e₂₃.inv)).natTrans.app N) ≫
        (conjugateIsoEquiv (adj₁₂'.comp adj₂₃') adj₁₃' c').hom.app (T₃.obj N) := by
  have key : (TwoSquare.mk _ _ _ _ e₁₃.inv : TwoSquare T₁ L₁₃ L₁₃' T₃) =
      ((TwoSquare.vComp (TwoSquare.mk _ _ _ _ e₁₂.inv : TwoSquare T₁ L₁₂ L₁₂' T₂)
        (TwoSquare.mk _ _ _ _ e₂₃.inv : TwoSquare T₂ L₂₃ L₂₃' T₃)).whiskerRight
          c'.hom).whiskerLeft c.inv := by
    ext M
    rw [← cancel_epi (e₁₃.hom.app M)]
    dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
      TwoSquare.natTrans, TwoSquare.mk]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc,
      Functor.comp_obj, Iso.hom_inv_id_app]
    rw [reassoc_of% h]
    simp [← Functor.map_comp, ← Functor.map_comp_assoc]
  have := NatTrans.congr_app (congrArg TwoSquare.natTrans
    (congrArg (mateEquiv adj₁₃ adj₁₃') key)) N
  rw [conjugateEquiv_mateEquiv_vcomp adj₁₃ (adj₁₂.comp adj₂₃) adj₁₃',
    mateEquiv_conjugateEquiv_vcomp (adj₁₂.comp adj₂₃) (adj₁₂'.comp adj₂₃') adj₁₃',
    mateEquiv_hcomp] at this
  rw [this]
  dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj]
  rw [← conjugateIsoEquiv_apply_inv]
  refine ((T₁.mapIso ((conjugateIsoEquiv (adj₁₂.comp adj₂₃) adj₁₃ c).app N)).hom_inv_id_assoc
    _).trans ?_
  rw [conjugateIsoEquiv_apply_hom, Category.assoc]

end Mates

end CategoryTheory
