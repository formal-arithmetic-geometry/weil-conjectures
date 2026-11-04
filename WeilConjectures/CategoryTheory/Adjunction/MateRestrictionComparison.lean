/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Comparing a geometric mate with an inverse scalar mate

Consider two pairs of adjunctions `L_E ⊣ G_E`, `L_F ⊣ G_F` (pullback/direct image) and two
scalar adjunctions `Ext_Y ⊣ Res_Y`, `Ext_X ⊣ Res_X`, together with a pullback comparison
`θ : Ext_Y ⋙ L_F ≅ L_E ⋙ Ext_X`. Suppose the restriction/direct-image comparison `δ` is the
mate of a restriction/pullback comparison `b` for other left adjoints `L'_E`, `L'_F` of the
same direct images, and suppose `θ` corresponds to `b` under the scalar units. Then the mate
of `θ` is the inverse scalar mate of `δ.inv`.

We also record that whether an inverse mate is invertible does not depend on the choice of
the left adjoints (`isIso_mateEquiv_symm_of_isIso`).
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

section ChangeOfAdjunction

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]

/-- Whether an inverse mate is invertible does not depend on the choice of left adjoints. -/
theorem isIso_mateEquiv_symm_of_isIso {G : A ⥤ C} {H : B ⥤ D} {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : L₁' ⊣ R₁)
    (b₂ : L₂' ⊣ R₂) (β : TwoSquare R₁ H G R₂) [IsIso ((mateEquiv b₁ b₂).symm β).natTrans] :
    IsIso ((mateEquiv a₁ a₂).symm β).natTrans := by
  let e₁ : L₁' ≅ L₁ := (conjugateIsoEquiv a₁ b₁).symm (Iso.refl R₁)
  let e₂ : L₂' ≅ L₂ := (conjugateIsoEquiv a₂ b₂).symm (Iso.refl R₂)
  have h₁ : conjugateEquiv a₁ b₁ e₁.hom = 𝟙 R₁ :=
    (conjugateEquiv a₁ b₁).apply_symm_apply (𝟙 R₁)
  have h₂ : conjugateEquiv a₂ b₂ e₂.hom = 𝟙 R₂ :=
    (conjugateEquiv a₂ b₂).apply_symm_apply (𝟙 R₂)
  let w := (mateEquiv a₁ a₂).symm β
  let w' := (mateEquiv b₁ b₂).symm β
  have h : w'.whiskerLeft e₁.hom = w.whiskerRight e₂.hom := by
    apply (mateEquiv a₁ b₂).injective
    rw [conjugateEquiv_mateEquiv_vcomp a₁ b₁ b₂ e₁.hom w',
      mateEquiv_conjugateEquiv_vcomp a₁ a₂ b₂ w e₂.hom]
    simp only [w, w', Equiv.apply_symm_apply, h₁, h₂]
    ext X
    simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom]
  have (X : A) : IsIso (w.natTrans.app X) := by
    have hc := congrArg (fun t ↦ t.natTrans.app X) h
    change w'.app X ≫ H.map (e₁.hom.app X) = e₂.hom.app (G.obj X) ≫ w.app X at hc
    have : IsIso (w'.natTrans.app X) := inferInstance
    have : IsIso (e₂.hom.app (G.obj X) ≫ w.app X) := by
      rw [← hc]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ this inferInstance
    exact IsIso.of_isIso_comp_left (e₂.hom.app (G.obj X)) (w.app X)
  exact NatIso.isIso_of_isIso_app _

end ChangeOfAdjunction

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {LE LE' : A ⥤ C} {GE : C ⥤ A} (PE : LE ⊣ GE) (PE' : LE' ⊣ GE)
  {LF LF' : B ⥤ D} {GF : D ⥤ B} (PF : LF ⊣ GF) (PF' : LF' ⊣ GF)
  {EY : A ⥤ B} {RY : B ⥤ A} (SY : EY ⊣ RY) {EX : C ⥤ D} {RX : D ⥤ C} (SX : EX ⊣ RX)

/-- The mate of a pullback comparison `θ` with respect to the pullback adjunctions equals the
inverse scalar mate of a restriction/direct-image comparison `δ`, once `δ` is the mate of a
restriction/pullback comparison `b` (for other left adjoints identified with the given ones by
`oE`, `oF`) and `θ` corresponds to `b` under the scalar units. -/
theorem mateEquiv_eq_mateEquiv_symm_of_unit
    (oE : LE ≅ LE') (oF : LF ≅ LF')
    (hoE : ∀ (M : A) (N : C) (t : LE.obj M ⟶ N),
      PE.homEquiv M N t = PE'.homEquiv M N (oE.inv.app M ≫ t))
    (hoF : ∀ (M : B) (N : D) (t : LF.obj M ⟶ N),
      PF.homEquiv M N t = PF'.homEquiv M N (oF.inv.app M ≫ t))
    (θ : EY ⋙ LF ≅ LE ⋙ EX) (b : LF' ⋙ RX ≅ RY ⋙ LE') (δ : GF ⋙ RY ≅ RX ⋙ GE)
    (hδ : ∀ (M : B) (N : D) (t : LF'.obj M ⟶ N),
      PE'.homEquiv _ _ (b.inv.app M ≫ RX.map t) =
        RY.map (PF'.homEquiv M N t) ≫ δ.hom.app N)
    (h : ∀ M : A, SX.unit.app (LE.obj M) ≫ RX.map (θ.inv.app M) =
      LE.map (SY.unit.app M) ≫ oE.hom.app _ ≫ b.inv.app (EY.obj M) ≫
        RX.map (oF.inv.app (EY.obj M))) :
    (mateEquiv PE PF (TwoSquare.mk _ _ _ _ θ.hom)).natTrans =
      ((mateEquiv SX SY).symm (TwoSquare.mk _ _ _ _ δ.inv)).natTrans := by
  have key (X : A) (N : D) (c : LF.obj (EY.obj X) ⟶ N) :
      PE.homEquiv _ _ (SX.homEquiv _ _ (θ.inv.app X ≫ c)) =
        SY.unit.app X ≫ RY.map (PF.homEquiv _ _ c) ≫ δ.hom.app N := by
    rw [hoE, hoF, ← hδ]
    erw [← PE'.homEquiv_naturality_left]
    rw [SX.homEquiv_unit, Functor.map_comp, reassoc_of% (h X)]
    simp
  have hconj : conjugateEquiv (SY.comp PF) (PE.comp SX) θ.inv = δ.hom := by
    ext N
    simpa [Adjunction.homEquiv_unit] using
      key _ N (LF.map (SY.counit.app (GF.obj N)) ≫ PF.counit.app N)
  have hconj' : conjugateEquiv (PE.comp SX) (SY.comp PF) θ.hom = δ.inv := by
    rw [← δ.comp_hom_eq_id, ← hconj]
    exact conjugateEquiv_comm _ _ θ.inv_hom_id
  rw [← hconj', ← iterated_mateEquiv_conjugateEquiv PE PF SY SX (TwoSquare.mk _ _ _ _ θ.hom)]
  exact (congrArg TwoSquare.natTrans ((mateEquiv SX SY).symm_apply_apply _)).symm

end CategoryTheory
