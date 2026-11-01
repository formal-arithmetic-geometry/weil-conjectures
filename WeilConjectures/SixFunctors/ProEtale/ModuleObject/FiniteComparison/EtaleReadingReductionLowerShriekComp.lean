/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoeffCompatibleMate

/-!
# Compatibility of a change of coefficients with reduction squares, under composition

Consider, over three "schemes" `1, 2, 3`, categories `K_i` (integral complexes), `A_i`, `B_i`
(complexes modulo two powers of `ℓ`), reductions `rA_i : K_i ⥤ A_i`, `rB_i : K_i ⥤ B_i`, a change
of coefficients `Ψ_i : A_i ⥤ B_i` left adjoint to `Res_i` and isomorphisms
`β_i : rA_i ⋙ Ψ_i ≅ rB_i`. For functors `F : K₁ ⥤ K₂`, `F_A`, `F_B` (think: `Rf_!`) with
reduction squares `γ_A : F ⋙ rA₂ ≅ rA₁ ⋙ F_A`, `γ_B : F ⋙ rB₂ ≅ rB₁ ⋙ F_B` and a coefficient
comparison `ι : Res₁ ⋙ F_A ≅ F_B ⋙ Res₂` with transpose `β_F : F_A ⋙ Ψ₂ ⟶ Ψ₁ ⋙ F_B`
(`AlgebraicGeometry.Etale.coeffMate`), the squares are *compatible with `β`*
(`AlgebraicGeometry.Etale.ReductionSquareCompatible`) if
`Ψ₂(γ_A K) ≫ β_F(rA₁ K) ≫ F_B(β₁ K) = β₂(F K) ≫ γ_B K`.

This file shows that compatibility is stable under composition
(`AlgebraicGeometry.Etale.ReductionSquareCompatible.comp`): for `H ≅ F ⋙ G` and compatible
composition isomorphisms on the coefficient side, the stacked squares of `F` and `G` are compatible
with `β` as soon as those of `F` and `G` are.
-/

@[expose] public section

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {K₁ K₂ K₃ A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category K₁] [Category K₂] [Category K₃]
  [Category A₁] [Category A₂] [Category A₃] [Category B₁] [Category B₂] [Category B₃]
  {rA₁ : K₁ ⥤ A₁} {rA₂ : K₂ ⥤ A₂} {rA₃ : K₃ ⥤ A₃} {rB₁ : K₁ ⥤ B₁} {rB₂ : K₂ ⥤ B₂}
  {rB₃ : K₃ ⥤ B₃} {Ψ₁ : A₁ ⥤ B₁} {Ψ₂ : A₂ ⥤ B₂} {Ψ₃ : A₃ ⥤ B₃} {Res₁ : B₁ ⥤ A₁}
  {Res₂ : B₂ ⥤ A₂} {Res₃ : B₃ ⥤ A₃} (adj₁ : Ψ₁ ⊣ Res₁) (adj₂ : Ψ₂ ⊣ Res₂) (adj₃ : Ψ₃ ⊣ Res₃)
  (β₁ : rA₁ ⋙ Ψ₁ ≅ rB₁) (β₂ : rA₂ ⋙ Ψ₂ ≅ rB₂) (β₃ : rA₃ ⋙ Ψ₃ ≅ rB₃)

/-- Reduction squares `γ_A : F ⋙ rA₂ ≅ rA₁ ⋙ F_A` and `γ_B : F ⋙ rB₂ ≅ rB₁ ⋙ F_B` are
*compatible with the changes of coefficients* `β_i : rA_i ⋙ Ψ_i ≅ rB_i` through the transpose
`β_F : F_A ⋙ Ψ₂ ⟶ Ψ₁ ⋙ F_B` of a coefficient comparison `ι` if
`Ψ₂(γ_A K) ≫ β_F(rA₁ K) ≫ F_B(β₁ K) = β₂(F K) ≫ γ_B K` for every `K`. -/
def ReductionSquareCompatible {F : K₁ ⥤ K₂} {FA : A₁ ⥤ A₂} {FB : B₁ ⥤ B₂}
    (ι : Res₁ ⋙ FA ≅ FB ⋙ Res₂) (γA : F ⋙ rA₂ ≅ rA₁ ⋙ FA) (γB : F ⋙ rB₂ ≅ rB₁ ⋙ FB) : Prop :=
  ∀ K, Ψ₂.map (γA.hom.app K) ≫ (coeffMate adj₁ adj₂ ι).app (rA₁.obj K) ≫ FB.map (β₁.hom.app K) =
    β₂.hom.app (F.obj K) ≫ γB.hom.app K

omit [Category K₃] [Category A₃] [Category B₃] in
lemma reductionSquareCompatible_iff {F : K₁ ⥤ K₂} {FA : A₁ ⥤ A₂} {FB : B₁ ⥤ B₂}
    (ι : Res₁ ⋙ FA ≅ FB ⋙ Res₂) (γA : F ⋙ rA₂ ≅ rA₁ ⋙ FA) (γB : F ⋙ rB₂ ≅ rB₁ ⋙ FB) :
    ReductionSquareCompatible adj₁ adj₂ β₁ β₂ ι γA γB ↔
      ∀ K, Ψ₂.map (γA.hom.app K) ≫ (coeffMate adj₁ adj₂ ι).app (rA₁.obj K) ≫
        FB.map (β₁.hom.app K) = β₂.hom.app (F.obj K) ≫ γB.hom.app K :=
  Iff.rfl

omit [Category K₃] [Category A₃] [Category B₃] in
/-- **Compatibility with the changes of coefficients, in restriction form**: writing
`T_i K := (rA_i K ⟶ Res_i Ψ_i rA_i K ⟶ Res_i rB_i K)` for the transposes of the `β_i` under
`Ψ_i ⊣ Res_i`, the squares are compatible iff `γ_A K ≫ F_A(T₁ K) ≫ ι(rB₁ K) = T₂(F K) ≫ Res₂(γ_B K)`
for every `K`. No change of coefficients `Ψ` appears in the right-hand side. -/
theorem reductionSquareCompatible_iff_unit {F : K₁ ⥤ K₂} {FA : A₁ ⥤ A₂} {FB : B₁ ⥤ B₂}
    (ι : Res₁ ⋙ FA ≅ FB ⋙ Res₂) (γA : F ⋙ rA₂ ≅ rA₁ ⋙ FA) (γB : F ⋙ rB₂ ≅ rB₁ ⋙ FB) :
    ReductionSquareCompatible adj₁ adj₂ β₁ β₂ ι γA γB ↔
      ∀ K, γA.hom.app K ≫ FA.map (adj₁.unit.app (rA₁.obj K) ≫ Res₁.map (β₁.hom.app K)) ≫
          ι.hom.app (rB₁.obj K) =
        (adj₂.unit.app (rA₂.obj (F.obj K)) ≫ Res₂.map (β₂.hom.app (F.obj K))) ≫
          Res₂.map (γB.hom.app K) := by
  have key (K : K₁) : adj₂.unit.app ((F ⋙ rA₂).obj K) ≫ Res₂.map (Ψ₂.map (γA.hom.app K) ≫
      (coeffMate adj₁ adj₂ ι).app (rA₁.obj K) ≫ FB.map (β₁.hom.app K)) =
      γA.hom.app K ≫ FA.map (adj₁.unit.app (rA₁.obj K) ≫ Res₁.map (β₁.hom.app K)) ≫
        ι.hom.app (rB₁.obj K) := by
    have hu := adj₂.unit.naturality (γA.hom.app K)
    have hc := unit_app_comp_map_coeffMate_app adj₁ adj₂ ι (rA₁.obj K)
    have hn := ι.hom.naturality (β₁.hom.app K)
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hu hc hn ⊢
    rw [Functor.map_comp, Functor.map_comp, ← reassoc_of% hu, reassoc_of% hc, ← hn,
      Functor.map_comp, Category.assoc]
  refine forall_congr' fun K ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← key, h, Functor.map_comp, Category.assoc]
    rfl
  · apply hom_ext_of_adjunction (adjA := adj₂)
    rw [key, h, Functor.map_comp, Category.assoc]
    rfl

variable {adj₁ adj₂ adj₃ β₁ β₂ β₃}

/-- **Compatibility with the changes of coefficients is stable under composition.** For
`e : H ≅ F ⋙ G`, `e_A : H_A ≅ F_A ⋙ G_A`, `e_B : H_B ≅ F_B ⋙ G_B` compatible with the coefficient
comparisons (`hι`), and reduction squares for `H` obtained by stacking those of `F` and `G`
(`hγA`, `hγB`), the squares of `H` are compatible with `β` if those of `F` and `G` are. -/
theorem ReductionSquareCompatible.comp {F : K₁ ⥤ K₂} {FA : A₁ ⥤ A₂} {FB : B₁ ⥤ B₂}
    {G : K₂ ⥤ K₃} {GA : A₂ ⥤ A₃} {GB : B₂ ⥤ B₃} {H : K₁ ⥤ K₃} {HA : A₁ ⥤ A₃} {HB : B₁ ⥤ B₃}
    {ιF : Res₁ ⋙ FA ≅ FB ⋙ Res₂} {ιG : Res₂ ⋙ GA ≅ GB ⋙ Res₃} {ιH : Res₁ ⋙ HA ≅ HB ⋙ Res₃}
    {γFA : F ⋙ rA₂ ≅ rA₁ ⋙ FA} {γFB : F ⋙ rB₂ ≅ rB₁ ⋙ FB} {γGA : G ⋙ rA₃ ≅ rA₂ ⋙ GA}
    {γGB : G ⋙ rB₃ ≅ rB₂ ⋙ GB} {γHA : H ⋙ rA₃ ≅ rA₁ ⋙ HA} {γHB : H ⋙ rB₃ ≅ rB₁ ⋙ HB}
    (hF : ReductionSquareCompatible adj₁ adj₂ β₁ β₂ ιF γFA γFB)
    (hG : ReductionSquareCompatible adj₂ adj₃ β₂ β₃ ιG γGA γGB)
    (e : H ≅ F ⋙ G) (eA : HA ≅ FA ⋙ GA) (eB : HB ≅ FB ⋙ GB)
    (hι : CoeffCompatible ιH (pasteTwoSquaresIso ιF ιG) eA.hom eB.hom)
    (hγA : ∀ K, γHA.inv.app K = eA.hom.app (rA₁.obj K) ≫ GA.map (γFA.inv.app K) ≫
      γGA.inv.app (F.obj K) ≫ rA₃.map (e.inv.app K))
    (hγB : ∀ K, γHB.inv.app K = eB.hom.app (rB₁.obj K) ≫ GB.map (γFB.inv.app K) ≫
      γGB.inv.app (F.obj K) ≫ rB₃.map (e.inv.app K)) :
    ReductionSquareCompatible adj₁ adj₃ β₁ β₃ ιH γHA γHB := by
  intro K
  have hA : γHA.hom.app K = rA₃.map (e.hom.app K) ≫ γGA.hom.app (F.obj K) ≫
      GA.map (γFA.hom.app K) ≫ eA.inv.app (rA₁.obj K) := by
    rw [← cancel_epi (γHA.inv.app K), Iso.inv_hom_id_app, hγA]
    simp [← Functor.map_comp_assoc]
  have hB : γHB.hom.app K = rB₃.map (e.hom.app K) ≫ γGB.hom.app (F.obj K) ≫
      GB.map (γFB.hom.app K) ≫ eB.inv.app (rB₁.obj K) := by
    rw [← cancel_epi (γHB.inv.app K), Iso.inv_hom_id_app, hγB]
    simp [← Functor.map_comp_assoc]
  -- the transpose of `ι_H` through `e_A`, `e_B`
  have hc : Ψ₃.map (eA.inv.app (rA₁.obj K)) ≫ (coeffMate adj₁ adj₃ ιH).app (rA₁.obj K) =
      (coeffMate adj₂ adj₃ ιG).app (FA.obj (rA₁.obj K)) ≫
        GB.map ((coeffMate adj₁ adj₂ ιF).app (rA₁.obj K)) ≫
          eB.inv.app (Ψ₁.obj (rA₁.obj K)) := by
    have h := hι.map_app_comp_coeffMate_app adj₁ adj₃ (rA₁.obj K)
    rw [coeffMate_pasteTwoSquaresIso_app adj₁ adj₂ adj₃] at h
    rw [← cancel_epi (Ψ₃.map (eA.hom.app (rA₁.obj K))), ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% h,
      Iso.hom_inv_id_app, Category.comp_id]
  have hnG := (coeffMate adj₂ adj₃ ιG).naturality (γFA.hom.app K)
  have hβ := β₃.hom.naturality (e.hom.app K)
  have hnB := eB.inv.naturality (β₁.hom.app K)
  have hFK := hF K
  have hGK := hG (F.obj K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnG hβ hnB hFK hGK ⊢
  rw [hA, hB, Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, Category.assoc, reassoc_of% hc, reassoc_of% hnG]
  rw [← hnB, ← GB.map_comp_assoc, ← GB.map_comp_assoc, Category.assoc, hFK, GB.map_comp_assoc,
    reassoc_of% hGK, reassoc_of% hβ]

omit [Category K₃] [Category A₃] [Category B₃] in
/-- **Compatibility with the changes of coefficients is invariant under a change of the
coefficient functors**: for isomorphisms `ε_A : F_A ≅ F_A'`, `ε_B : F_B ≅ F_B'` compatible with the
coefficient comparisons `ι` and `ι'`, the squares `γ_A`, `γ_B` are compatible with `β` through
`ι` iff the squares `γ_A' = γ_A ≫ ε_A`, `γ_B' = γ_B ≫ ε_B` are through `ι'`; here is the direction
from `ι` to `ι'`. -/
theorem ReductionSquareCompatible.of_coeffCompatible {F : K₁ ⥤ K₂} {FA FA' : A₁ ⥤ A₂}
    {FB FB' : B₁ ⥤ B₂} {ι : Res₁ ⋙ FA ≅ FB ⋙ Res₂} {ι' : Res₁ ⋙ FA' ≅ FB' ⋙ Res₂}
    {γA : F ⋙ rA₂ ≅ rA₁ ⋙ FA} {γB : F ⋙ rB₂ ≅ rB₁ ⋙ FB} {γA' : F ⋙ rA₂ ≅ rA₁ ⋙ FA'}
    {γB' : F ⋙ rB₂ ≅ rB₁ ⋙ FB'} (h : ReductionSquareCompatible adj₁ adj₂ β₁ β₂ ι γA γB)
    (εA : FA ≅ FA') (εB : FB ≅ FB') (hε : CoeffCompatible ι ι' εA.hom εB.hom)
    (hγA : ∀ K, γA'.hom.app K = γA.hom.app K ≫ εA.hom.app (rA₁.obj K))
    (hγB : ∀ K, γB'.hom.app K = γB.hom.app K ≫ εB.hom.app (rB₁.obj K)) :
    ReductionSquareCompatible adj₁ adj₂ β₁ β₂ ι' γA' γB' := by
  intro K
  have hc := hε.map_app_comp_coeffMate_app adj₁ adj₂ (rA₁.obj K)
  have hn := εB.hom.naturality (β₁.hom.app K)
  have hK := h K
  dsimp only [Functor.comp_obj] at hn hK ⊢
  rw [hγA, hγB, Functor.map_comp, Category.assoc, reassoc_of% hc, ← hn, reassoc_of% hK]

omit [Category K₃] [Category A₃] [Category B₃] in
/-- The direction of `AlgebraicGeometry.Etale.ReductionSquareCompatible.of_coeffCompatible` from
the squares `γ ≪≫ ε` (through `ι'`) back to the squares `γ` (through `ι`). -/
theorem ReductionSquareCompatible.of_trans_isoWhiskerLeft {F : K₁ ⥤ K₂} {FA FA' : A₁ ⥤ A₂}
    {FB FB' : B₁ ⥤ B₂} {ι : Res₁ ⋙ FA ≅ FB ⋙ Res₂} {ι' : Res₁ ⋙ FA' ≅ FB' ⋙ Res₂}
    {γA : F ⋙ rA₂ ≅ rA₁ ⋙ FA} {γB : F ⋙ rB₂ ≅ rB₁ ⋙ FB} {εA : FA ≅ FA'} {εB : FB ≅ FB'}
    (h : ReductionSquareCompatible adj₁ adj₂ β₁ β₂ ι' (γA ≪≫ Functor.isoWhiskerLeft rA₁ εA)
      (γB ≪≫ Functor.isoWhiskerLeft rB₁ εB))
    (hε : CoeffCompatible ι' ι εA.inv εB.inv) :
    ReductionSquareCompatible adj₁ adj₂ β₁ β₂ ι γA γB :=
  h.of_coeffCompatible εA.symm εB.symm hε (fun K ↦ by simp) (fun K ↦ by simp)

section Mates

variable {CX CY A₁X A₁Y A₂X A₂Y : Type*} [Category CX] [Category CY] [Category A₁X]
  [Category A₁Y] [Category A₂X] [Category A₂Y] {Lc : CX ⥤ CY} {Rc : CY ⥤ CX}
  {rX₁ : CX ⥤ A₁X} {rY₁ : CY ⥤ A₁Y} {rX₂ : CX ⥤ A₂X} {rY₂ : CY ⥤ A₂Y} {L₁ : A₁X ⥤ A₁Y}
  {R₁ : A₁Y ⥤ A₁X} {L₂ : A₂X ⥤ A₂Y} {R₂ : A₂Y ⥤ A₂X} {ΨX : A₁X ⥤ A₂X} {ΨY : A₁Y ⥤ A₂Y}

/-- **Compatibilities of comparison squares can be checked on their mates**: the converse of
`CategoryTheory.map_mateEquiv_app_comp_mateEquiv_app_comp_map_eq`. If the isomorphisms
`β_X : r_X¹ ⋙ Ψ_X ≅ r_X²` and `β_Y : r_Y¹ ⋙ Ψ_Y ≅ r_Y²` intertwine the mates of the `γᵢ⁻¹`
under `L_c ⊣ R_c`, `Lᵢ ⊣ Rᵢ` through the mate of `β_f⁻¹`, then they intertwine the comparisons
`γᵢ : L_c ⋙ r_Yⁱ ≅ r_Xⁱ ⋙ Lᵢ` through `β_f : L₁ ⋙ Ψ_Y ⟶ Ψ_X ⋙ L₂`. -/
lemma map_app_comp_app_comp_map_eq_of_mateEquiv (adjc : Lc ⊣ Rc) (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (γ₁ : Lc ⋙ rY₁ ≅ rX₁ ⋙ L₁) (γ₂ : Lc ⋙ rY₂ ≅ rX₂ ⋙ L₂)
    (βf : L₁ ⋙ ΨY ⟶ ΨX ⋙ L₂) [IsIso βf] (βX : rX₁ ⋙ ΨX ≅ rX₂) (βY : rY₁ ⋙ ΨY ≅ rY₂)
    (h : ∀ N, ΨX.map ((mateEquiv adjc adj₁ (TwoSquare.mk _ _ _ _ γ₁.inv)).natTrans.app N) ≫
        (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ (inv βf))).natTrans.app (rY₁.obj N) ≫
          R₂.map (βY.hom.app N) =
      βX.hom.app (Rc.obj N) ≫ (mateEquiv adjc adj₂ (TwoSquare.mk _ _ _ _ γ₂.inv)).natTrans.app N)
    (K : CX) :
    ΨY.map (γ₁.hom.app K) ≫ βf.app (rX₁.obj K) ≫ L₂.map (βX.hom.app K) =
      βY.hom.app (Lc.obj K) ≫ γ₂.hom.app K := by
  -- the inverted compatibility, checked on transposes under `L₂ ⊣ R₂`
  have h' : (inv βf).app (rX₁.obj K) ≫ ΨY.map (γ₁.inv.app K) ≫ βY.hom.app (Lc.obj K) =
      L₂.map (βX.hom.app K) ≫ γ₂.inv.app K := by
    let m₁ := (mateEquiv adjc adj₁ (TwoSquare.mk _ _ _ _ γ₁.inv)).natTrans
    let m₂ := (mateEquiv adjc adj₂ (TwoSquare.mk _ _ _ _ γ₂.inv)).natTrans
    let m₃ := (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ (inv βf))).natTrans
    have u₁ : rX₁.map (adjc.unit.app K) ≫ m₁.app (Lc.obj K) =
        adj₁.unit.app (rX₁.obj K) ≫ R₁.map (γ₁.inv.app K) :=
      unit_mateEquiv adjc adj₁ (TwoSquare.mk _ _ _ _ γ₁.inv) K
    have u₂ : rX₂.map (adjc.unit.app K) ≫ m₂.app (Lc.obj K) =
        adj₂.unit.app (rX₂.obj K) ≫ R₂.map (γ₂.inv.app K) :=
      unit_mateEquiv adjc adj₂ (TwoSquare.mk _ _ _ _ γ₂.inv) K
    have u₃ : ΨX.map (adj₁.unit.app (rX₁.obj K)) ≫ m₃.app (L₁.obj (rX₁.obj K)) =
        adj₂.unit.app (ΨX.obj (rX₁.obj K)) ≫ R₂.map ((inv βf).app (rX₁.obj K)) :=
      unit_mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ (inv βf)) (rX₁.obj K)
    have n₁ : βX.hom.app K ≫ adj₂.unit.app (rX₂.obj K) =
        adj₂.unit.app (ΨX.obj (rX₁.obj K)) ≫ R₂.map (L₂.map (βX.hom.app K)) :=
      adj₂.unit.naturality (βX.hom.app K)
    have n₂ : ΨX.map (R₁.map (γ₁.inv.app K)) ≫ m₃.app (rY₁.obj (Lc.obj K)) =
        m₃.app (L₁.obj (rX₁.obj K)) ≫ R₂.map (ΨY.map (γ₁.inv.app K)) :=
      m₃.naturality (γ₁.inv.app K)
    have n₃ : ΨX.map (rX₁.map (adjc.unit.app K)) ≫ βX.hom.app (Rc.obj (Lc.obj K)) =
        βX.hom.app K ≫ rX₂.map (adjc.unit.app K) :=
      βX.hom.naturality (adjc.unit.app K)
    have hK : ΨX.map (m₁.app (Lc.obj K)) ≫ m₃.app (rY₁.obj (Lc.obj K)) ≫
        R₂.map (βY.hom.app (Lc.obj K)) = βX.hom.app (Rc.obj (Lc.obj K)) ≫ m₂.app (Lc.obj K) :=
      h (Lc.obj K)
    apply (adj₂.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, ← Category.assoc, ← u₃, Category.assoc, ← reassoc_of% n₂,
      ← ΨX.map_comp_assoc, ← u₁, ΨX.map_comp, Category.assoc, hK, reassoc_of% n₃, u₂,
      reassoc_of% n₁]
  have e := congrArg
    (fun t ↦ ΨY.map (γ₁.hom.app K) ≫ βf.app (rX₁.obj K) ≫ t ≫ γ₂.hom.app K) h'
  have e₁ : βf.app (rX₁.obj K) ≫ (inv βf).app (rX₁.obj K) = 𝟙 _ := by
    rw [← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app]
  simp only [Category.assoc, Iso.inv_hom_id_app] at e
  rw [reassoc_of% e₁, ← ΨY.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp] at e
  rw [e]
  simp

end Mates

end AlgebraicGeometry.Etale
