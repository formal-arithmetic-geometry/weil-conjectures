/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transporting compatibilities of comparison squares to their mates

Consider a functor `L_c : C_X ⥤ C_Y` with right adjoint `R_c`, two "readings" of it, i.e. functors
`L₁ : D_X¹ ⥤ D_Y¹` and `L₂ : D_X² ⥤ D_Y²` with right adjoints `R₁`, `R₂`, together with
comparison isomorphisms `γᵢ : L_c ⋙ r_Yⁱ ≅ r_Xⁱ ⋙ Lᵢ` for functors `r_Xⁱ : C_X ⥤ D_Xⁱ`,
`r_Yⁱ : C_Y ⥤ D_Yⁱ`. Let `Ψ_X : D_X¹ ⥤ D_X²` and `Ψ_Y : D_Y¹ ⥤ D_Y²` be functors with a comparison
`β_f : L₁ ⋙ Ψ_Y ⟶ Ψ_X ⋙ L₂` and isomorphisms `β_X : r_X¹ ⋙ Ψ_X ≅ r_X²`, `β_Y : r_Y¹ ⋙ Ψ_Y ≅ r_Y²`.

If `β_X`, `β_Y` intertwine `γ₁` with `γ₂` through `β_f`, then they intertwine the mates
`R_c ⋙ r_Xⁱ ⟶ r_Yⁱ ⋙ Rᵢ` of the `γᵢ⁻¹` through the mate `R₁ ⋙ Ψ_X ⟶ Ψ_Y ⋙ R₂` of `β_f⁻¹`
(`CategoryTheory.map_mateEquiv_app_comp_mateEquiv_app_comp_map_eq`).

This is used (blueprint `det-sp-purity-coefficient-change`) to deduce the compatibility of the
reduction of coefficients `Ψ` with the comparisons for `Rf^!` from the one for `Rf_!`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {CX CY DX₁ DY₁ DX₂ DY₂ : Type*} [Category CX] [Category CY] [Category DX₁]
  [Category DY₁] [Category DX₂] [Category DY₂]
  {Lc : CX ⥤ CY} {Rc : CY ⥤ CX} (adjc : Lc ⊣ Rc)
  {L₁ : DX₁ ⥤ DY₁} {R₁ : DY₁ ⥤ DX₁} (adj₁ : L₁ ⊣ R₁)
  {L₂ : DX₂ ⥤ DY₂} {R₂ : DY₂ ⥤ DX₂} (adj₂ : L₂ ⊣ R₂)
  {rX₁ : CX ⥤ DX₁} {rY₁ : CY ⥤ DY₁} {rX₂ : CX ⥤ DX₂} {rY₂ : CY ⥤ DY₂}
  {ΨX : DX₁ ⥤ DX₂} {ΨY : DY₁ ⥤ DY₂}

/-- **Compatibilities of comparison squares pass to their mates.** If the isomorphisms
`β_X : r_X¹ ⋙ Ψ_X ≅ r_X²` and `β_Y : r_Y¹ ⋙ Ψ_Y ≅ r_Y²` intertwine the comparisons
`γᵢ : L_c ⋙ r_Yⁱ ≅ r_Xⁱ ⋙ Lᵢ` through `β_f : L₁ ⋙ Ψ_Y ⟶ Ψ_X ⋙ L₂`, then they intertwine the mates
of the `γᵢ⁻¹` under `L_c ⊣ R_c`, `Lᵢ ⊣ Rᵢ` through the mate of `β_f⁻¹` under `L₁ ⊣ R₁`,
`L₂ ⊣ R₂`. -/
lemma map_mateEquiv_app_comp_mateEquiv_app_comp_map_eq (γ₁ : Lc ⋙ rY₁ ≅ rX₁ ⋙ L₁)
    (γ₂ : Lc ⋙ rY₂ ≅ rX₂ ⋙ L₂) (βf : L₁ ⋙ ΨY ⟶ ΨX ⋙ L₂) [IsIso βf] (βX : rX₁ ⋙ ΨX ≅ rX₂)
    (βY : rY₁ ⋙ ΨY ≅ rY₂)
    (h : ∀ K, ΨY.map (γ₁.hom.app K) ≫ βf.app (rX₁.obj K) ≫ L₂.map (βX.hom.app K) =
      βY.hom.app (Lc.obj K) ≫ γ₂.hom.app K) (N : CY) :
    ΨX.map ((mateEquiv adjc adj₁ (TwoSquare.mk _ _ _ _ γ₁.inv)).natTrans.app N) ≫
        (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ (inv βf))).natTrans.app (rY₁.obj N) ≫
          R₂.map (βY.hom.app N) =
      βX.hom.app (Rc.obj N) ≫
        (mateEquiv adjc adj₂ (TwoSquare.mk _ _ _ _ γ₂.inv)).natTrans.app N := by
  -- the inverted compatibility at `R_c N`
  have h' : (inv βf).app (rX₁.obj (Rc.obj N)) ≫ ΨY.map (γ₁.inv.app (Rc.obj N)) ≫
      βY.hom.app (Lc.obj (Rc.obj N)) = L₂.map (βX.hom.app (Rc.obj N)) ≫ γ₂.inv.app (Rc.obj N) := by
    have h₀ := h (Rc.obj N)
    rw [← cancel_epi (βf.app (rX₁.obj (Rc.obj N))), ← NatTrans.comp_app_assoc, IsIso.hom_inv_id, NatTrans.id_app,
      Category.id_comp,
      ← cancel_epi (ΨY.map (γ₁.hom.app (Rc.obj N))), ← ΨY.map_comp_assoc, Iso.hom_inv_id_app,
      ΨY.map_id, Category.id_comp, reassoc_of% h₀, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  apply (adj₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  have m₁ := mateEquiv_counit adjc adj₁ (TwoSquare.mk _ _ _ _ γ₁.inv) N
  have m₂ := mateEquiv_counit adjc adj₂ (TwoSquare.mk _ _ _ _ γ₂.inv) N
  have m₃ := mateEquiv_counit adj₁ adj₂ (TwoSquare.mk _ _ _ _ (inv βf)) (rY₁.obj N)
  have n₁ := adj₂.counit.naturality (βY.hom.app N)
  have n₂ := (inv βf).naturality ((mateEquiv adjc adj₁ (TwoSquare.mk _ _ _ _ γ₁.inv)).natTrans.app N)
  have n₃ := βY.hom.naturality (adjc.counit.app N)
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at m₁ m₂ m₃ n₁ n₂ n₃
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, n₁, reassoc_of% m₃,
    reassoc_of% n₂, ← ΨY.map_comp_assoc, m₁, ΨY.map_comp, Category.assoc, n₃, Functor.map_comp,
    Category.assoc, m₂, reassoc_of% h']

/-- **Splitting a compatibility along a natural comparison.** For a comparison
`c : R₁ ⋙ Ψ_A ⟶ Ψ_B ⋙ R₂` and morphisms `U : W ⟶ R₁ M`, `U' : W' ⟶ R₂ M'`, `ν : M ⟶ N`,
`ν' : M' ⟶ N'`, if `Ψ U` corresponds to `U'` through `c` and `b_M`, and `Ψ ν` corresponds to `ν'`
through `b_M` and `e`, then `Ψ(U ≫ R₁ ν)` corresponds to `U' ≫ R₂ ν'` through `c` and `e`. This
splits the compatibility of `Ψ` with the identifications `red(Rf^! 𝒪) ≅ Rf^!(red 𝒪) ≅ Rf^! Λ` into
the one with `Rf^!` and the one with the units. -/
lemma map_comp_map_app_comp_map_eq {A₁ A₂ B₁ B₂ : Type*} [Category A₁] [Category A₂]
    [Category B₁] [Category B₂] {ΨA : A₁ ⥤ A₂} {ΨB : B₁ ⥤ B₂} {R₁ : B₁ ⥤ A₁} {R₂ : B₂ ⥤ A₂}
    (c : R₁ ⋙ ΨA ⟶ ΨB ⋙ R₂) {W : A₁} {W' : A₂} {M N : B₁} {M' N' : B₂} (U : W ⟶ R₁.obj M)
    (U' : W' ⟶ R₂.obj M') (ν : M ⟶ N) (ν' : M' ⟶ N') (bW : ΨA.obj W ⟶ W') (bM : ΨB.obj M ⟶ M')
    (e : ΨB.obj N ⟶ N') (hU : ΨA.map U ≫ c.app M ≫ R₂.map bM = bW ≫ U')
    (hν : ΨB.map ν ≫ e = bM ≫ ν') :
    ΨA.map (U ≫ R₁.map ν) ≫ c.app N ≫ R₂.map e = bW ≫ U' ≫ R₂.map ν' := by
  have hc := c.naturality ν
  simp only [Functor.comp_obj, Functor.comp_map] at hc
  rw [Functor.map_comp, Category.assoc, reassoc_of% hc, ← R₂.map_comp, hν, R₂.map_comp,
    reassoc_of% hU]

end CategoryTheory
