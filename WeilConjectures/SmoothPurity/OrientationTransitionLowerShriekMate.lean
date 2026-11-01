/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Transposing a compatibility of reduction squares along the adjunctions

Consider adjunctions `L₁ ⊣ R₁`, `L ⊣ R` and `L' ⊣ R'`, functors `r_U, r_X` (towards the sources and
targets of `L`) and `r'_U, r'_X` (towards those of `L'`), functors `Res_U, Res_X` from the
categories of `L'` to those of `L`, and transformations `T_U : r_U ⟶ r'_U ⋙ Res_U`,
`T_X : r_X ⟶ r'_X ⋙ Res_X`. A square `ι : Res_U ⋙ L ⟶ L' ⋙ Res_X` and squares
`θ : r_U ⋙ L ⟶ L₁ ⋙ r_X`, `θ' : r'_U ⋙ L' ⟶ L₁ ⋙ r'_X` are compatible through `T` as soon as
their mates `R₁ ⋙ r_U ⟶ r_X ⋙ R`, `R₁ ⋙ r'_U ⟶ r'_X ⋙ R'` and `R' ⋙ Res_U ⟶ Res_X ⋙ R` are
(`CategoryTheory.map_app_comp_app_comp_map_app_eq_of_mateEquiv`). This is used, in blueprint
`det-sp-purity-coefficient-change`, to reduce the compatibility of the reduction comparisons for
`Rj_!` along an open immersion `j` to the one for `j^*`.
-/

@[expose] public section

namespace CategoryTheory

variable {C₁ C₂ A₁ A₂ B₁ B₂ : Type*} [Category* C₁] [Category* C₂] [Category* A₁] [Category* A₂]
  [Category* B₁] [Category* B₂] {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} (a₁ : L₁ ⊣ R₁) {L : A₁ ⥤ A₂}
  {R : A₂ ⥤ A₁} (b : L ⊣ R) {L' : B₁ ⥤ B₂} {R' : B₂ ⥤ B₁} (b' : L' ⊣ R') {r₁ : C₁ ⥤ A₁}
  {r₂ : C₂ ⥤ A₂} {r₁' : C₁ ⥤ B₁} {r₂' : C₂ ⥤ B₂} {S₁ : B₁ ⥤ A₁} {S₂ : B₂ ⥤ A₂}

/-- **Compatibility of transposed squares through transformations `T`**: if the mates
`R₁ ⋙ r₁ ⟶ r₂ ⋙ R`, `R₁ ⋙ r₁' ⟶ r₂' ⋙ R'` of `θ`, `θ'` and the mate `R' ⋙ S₁ ⟶ S₂ ⋙ R` of `ι`
are compatible through `T₁ : r₁ ⟶ r₁' ⋙ S₁` and `T₂ : r₂ ⟶ r₂' ⋙ S₂`, then so are `θ`, `θ'` and
`ι`. -/
theorem map_app_comp_app_comp_map_app_eq_of_mateEquiv (T₁ : r₁ ⟶ r₁' ⋙ S₁) (T₂ : r₂ ⟶ r₂' ⋙ S₂)
    (ι : TwoSquare S₁ L' L S₂) (θ : TwoSquare r₁ L₁ L r₂) (θ' : TwoSquare r₁' L₁ L' r₂')
    (h : ∀ N : C₂, T₁.app (R₁.obj N) ≫ S₁.map ((mateEquiv a₁ b' θ').app N) ≫
        (mateEquiv b' b ι).app (r₂'.obj N) =
      (mateEquiv a₁ b θ).app N ≫ R.map (T₂.app N))
    (K : C₁) :
    L.map (T₁.app K) ≫ ι.app (r₁'.obj K) ≫ S₂.map (θ'.app K) = θ.app K ≫ T₂.app (L₁.obj K) := by
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have h₁ := unit_mateEquiv b' b ι (r₁'.obj K)
  have h₂ := (mateEquiv b' b ι).natTrans.naturality (θ'.app K)
  have h₃ := unit_mateEquiv a₁ b' θ' K
  have h₄ := T₁.naturality (a₁.unit.app K)
  have h₅ := unit_mateEquiv a₁ b θ K
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at h₁ h₂ h₃ h₄ h₅
  rw [b.unit_naturality_assoc]
  erw [← reassoc_of% h₁]
  erw [← h₂]
  rw [← S₁.map_comp_assoc]
  erw [← h₃]
  rw [S₁.map_comp_assoc, ← reassoc_of% h₄, h, reassoc_of% h₅]

/-- The isomorphism of right adjoints induced by an isomorphism `ε : L ≅ L₂` of left adjoints is
the conjugate of `ε⁻¹`. -/
lemma Adjunction.rightAdjointUniq_ofNatIsoLeft_symm_hom {L₂ : A₁ ⥤ A₂} {R₂ : A₂ ⥤ A₁}
    (b₂ : L₂ ⊣ R₂) (ε : L ≅ L₂) :
    (b.rightAdjointUniq (b₂.ofNatIsoLeft ε.symm)).hom = conjugateEquiv b b₂ ε.inv := by
  ext Y
  simp [Adjunction.rightAdjointUniq, Adjunction.ofNatIsoLeft]

/-- The mate of a square `θ : r₁ ⋙ L ⟶ L₁ ⋙ r₂` precomposed with an isomorphism `ε : L ≅ L₂`,
under the adjunction `L₂ ⊣ R₂`, is the mate of `θ` under `L ⊣ R` followed by the induced
isomorphism `R ≅ R₂` of right adjoints. -/
theorem mateEquiv_whiskerRight_inv_app {L₂ : A₁ ⥤ A₂} {R₂ : A₂ ⥤ A₁} (b₂ : L₂ ⊣ R₂)
    (ε : L ≅ L₂) (θ : TwoSquare r₁ L₁ L r₂) (N : C₂) :
    (mateEquiv a₁ b₂ (θ.whiskerRight ε.inv)).app N =
      (mateEquiv a₁ b θ).app N ≫
        (b.rightAdjointUniq (b₂.ofNatIsoLeft ε.symm)).hom.app (r₂.obj N) := by
  rw [mateEquiv_conjugateEquiv_vcomp a₁ b b₂ θ ε.inv,
    Adjunction.rightAdjointUniq_ofNatIsoLeft_symm_hom]
  rfl
/-- **Compatibility of squares through transformations `T`, transported to the mates**: the
converse of `CategoryTheory.map_app_comp_app_comp_map_app_eq_of_mateEquiv`. If the squares
`θ : r₁ ⋙ L ⟶ L₁ ⋙ r₂`, `θ' : r₁' ⋙ L' ⟶ L₁ ⋙ r₂'` and `ι : S₁ ⋙ L ⟶ L' ⋙ S₂` are compatible
through `T₁ : r₁ ⟶ r₁' ⋙ S₁` and `T₂ : r₂ ⟶ r₂' ⋙ S₂`, then so are their mates
`R₁ ⋙ r₁ ⟶ r₂ ⋙ R`, `R₁ ⋙ r₁' ⟶ r₂' ⋙ R'` and `R' ⋙ S₁ ⟶ S₂ ⋙ R`. -/
theorem app_comp_map_mateEquiv_app_comp_mateEquiv_app_eq_of_map (T₁ : r₁ ⟶ r₁' ⋙ S₁)
    (T₂ : r₂ ⟶ r₂' ⋙ S₂) (ι : TwoSquare S₁ L' L S₂) (θ : TwoSquare r₁ L₁ L r₂)
    (θ' : TwoSquare r₁' L₁ L' r₂')
    (h : ∀ K : C₁, L.map (T₁.app K) ≫ ι.app (r₁'.obj K) ≫ S₂.map (θ'.app K) =
      θ.app K ≫ T₂.app (L₁.obj K))
    (N : C₂) :
    T₁.app (R₁.obj N) ≫ S₁.map ((mateEquiv a₁ b' θ').app N) ≫
        (mateEquiv b' b ι).app (r₂'.obj N) =
      (mateEquiv a₁ b θ).app N ≫ R.map (T₂.app N) := by
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have h₁ := mateEquiv_counit b' b ι (r₂'.obj N)
  have h₂ := ι.natTrans.naturality ((mateEquiv a₁ b' θ').app N)
  have h₃ := mateEquiv_counit a₁ b' θ' N
  have h₄ := T₂.naturality (a₁.counit.app N)
  have h₅ := mateEquiv_counit a₁ b θ N
  have hK := h (R₁.obj N)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at h₁ h₂ h₃ h₄ h₅ hK
  rw [h₁]
  erw [reassoc_of% h₂]
  rw [← S₂.map_comp, h₃, S₂.map_comp, reassoc_of% hK, ← h₄, b.counit_naturality, reassoc_of% h₅]

end CategoryTheory
