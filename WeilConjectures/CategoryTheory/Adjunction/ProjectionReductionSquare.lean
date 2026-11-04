/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.PoincareDuality.Abstract
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Reduction squares for projection morphisms

Let `r : 𝒜 ⥤ 𝒮` be "reduction" functors from monoidal categories to categories carrying a
tensor bifunctor `T : 𝒮 × 𝒮 ⥤ 𝒮`, with tensor comparisons `μ : r (A ⊗ B) ≅ T (r A, r B)`.
Given adjunctions `L ⊣ R` on the monoidal side and `G ⊣ P` on the reduced side, together with
a reduction comparison `pull : L ⋙ r' ≅ r ⋙ G` and a tensor comparison
`sp : G (T (a, b)) ≅ T (G a, G b)`, this file shows that the projection morphisms on both sides
are intertwined by the reduction, as soon as `pull` is compatible with the tensor comparisons.

## Main results

* `CategoryTheory.Adjunction.projectionMorphism_reduction_square`: the proper square, for the
  projection morphism of `L ⊣ R` and the right adjoint projection map of `G ⊣ P`, transported
  along the mate of `pull`.
* `CategoryTheory.Adjunction.projectionComparison_reduction_square`: the open square, for the
  projection comparison of `I ⊣ L` and the transpose of `unit ⊗ id` along `J ⊣ G`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Adjunction

section ProperSquare

universe v₁ v₂ u₁ u₂

variable {AY AZ : Type u₁} {SY SZ : Type u₂} [Category.{v₁} AY] [Category.{v₁} AZ]
  [Category.{v₂} SY] [Category.{v₂} SZ]
  [MonoidalCategory AY] [MonoidalCategory AZ]
  {TY : SY × SY ⥤ SY} {TZ : SZ × SZ ⥤ SZ} {rY : AY ⥤ SY} {rZ : AZ ⥤ SZ}
  (muY : Functor.uncurry.obj (curriedTensor AY) ⋙ rY ≅ (rY.prod rY) ⋙ TY)
  (muZ : Functor.uncurry.obj (curriedTensor AZ) ⋙ rZ ≅ (rZ.prod rZ) ⋙ TZ)
  {Lg : AY ⥤ AZ} {Rg : AZ ⥤ AY} (adjG : Lg ⊣ Rg) [Lg.Monoidal]
  {Gg : SY ⥤ SZ} {Pg : SZ ⥤ SY} (gadj : Gg ⊣ Pg)
  (spG : TY ⋙ Gg ≅ (Gg.prod Gg) ⋙ TZ) (pullG : Lg ⋙ rZ ≅ rY ⋙ Gg)

/-- The proper reduction square: if the reduction comparison `pullG` is compatible with the
oplax structure of `Lg` and the tensor comparisons, then the reduction of the projection
morphism of `Lg ⊣ Rg`, followed by the mate of `pullG`, is the right adjoint projection map
of `Gg ⊣ Pg`. -/
theorem projectionMorphism_reduction_square
    (h : ∀ A B : AY, rZ.map (Functor.OplaxMonoidal.δ Lg A B) ≫ muZ.hom.app (Lg.obj A, Lg.obj B) ≫
      TZ.map (Prod.mkHom (pullG.hom.app A) (pullG.hom.app B)) =
      pullG.hom.app (A ⊗ B) ≫ Gg.map (muY.hom.app (A, B)) ≫
        spG.hom.app (rY.obj A, rY.obj B))
    (A : AZ) (K : AY) :
    rY.map (adjG.projectionMorphism A K) ≫
        (mateEquiv adjG gadj (TwoSquare.mk _ _ _ _ pullG.inv)).natTrans.app (A ⊗ Lg.obj K) ≫
        Pg.map (muZ.hom.app (A, Lg.obj K) ≫ TZ.map (Prod.mkHom (𝟙 _) (pullG.hom.app K))) =
      muY.hom.app (Rg.obj A, K) ≫
        TY.map (Prod.mkHom
          ((mateEquiv adjG gadj (TwoSquare.mk _ _ _ _ pullG.inv)).natTrans.app A) (𝟙 _)) ≫
        ((gadj.rightAdjointProjectionMap (T_C := Functor.curryObj TZ) (T_D := Functor.curryObj TY)
          (Functor.curry.mapIso spG ≪≫
          Functor.curryObjProdComp Gg Gg TZ).hom).app (rZ.obj A)).app (rY.obj K) := by
  have hc (B : AZ) :
      Gg.map ((mateEquiv adjG gadj (TwoSquare.mk _ _ _ _ pullG.inv)).natTrans.app B) ≫
      gadj.counit.app (rZ.obj B) = pullG.inv.app (Rg.obj B) ≫ rZ.map (adjG.counit.app B) :=
    mateEquiv_counit adjG gadj (TwoSquare.mk _ _ _ _ pullG.inv) B
  have hsp (a : SZ) (L : SY) : Gg.map (((gadj.rightAdjointProjectionMap
      (T_C := Functor.curryObj TZ) (T_D := Functor.curryObj TY)
      (Functor.curry.mapIso spG ≪≫ Functor.curryObjProdComp Gg Gg TZ).hom).app a).app L) ≫
      gadj.counit.app (TZ.obj (a, Gg.obj L)) =
      spG.hom.app (Pg.obj a, L) ≫ TZ.map (Prod.mkHom (gadj.counit.app a) (𝟙 _)) := by
    refine (map_rightAdjointProjectionMap_app_app_comp_counit gadj (T_C := Functor.curryObj TZ)
      (T_D := Functor.curryObj TY)
      (Functor.curry.mapIso spG ≪≫ Functor.curryObjProdComp Gg Gg TZ).hom a L).trans ?_
    simp
    rfl
  have h' (B C : AY) : pullG.inv.app (B ⊗ C) ≫ rZ.map (Functor.OplaxMonoidal.δ Lg B C) ≫
      muZ.hom.app (Lg.obj B, Lg.obj C) =
      Gg.map (muY.hom.app (B, C)) ≫ spG.hom.app (rY.obj B, rY.obj C) ≫
        TZ.map (Prod.mkHom (pullG.inv.app B) (pullG.inv.app C)) := by
    rw [← cancel_epi (pullG.hom.app (B ⊗ C)), Iso.hom_inv_id_app_assoc, ← reassoc_of% (h B C),
      ← TZ.map_comp]
    simp only [prod_comp, Iso.hom_inv_id_app, Functor.comp_obj]
    rw [← prod_id]
    erw [TZ.map_id]
    rw [Category.comp_id]
  generalize (mateEquiv adjG gadj (TwoSquare.mk _ _ _ _ pullG.inv)).natTrans = pS at hc ⊢
  generalize gadj.rightAdjointProjectionMap (T_C := Functor.curryObj TZ)
      (T_D := Functor.curryObj TY)
      (Functor.curry.mapIso spG ≪≫ Functor.curryObjProdComp Gg Gg TZ).hom = sP at hsp ⊢
  apply (gadj.homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit]
  dsimp only [Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc, gadj.counit_naturality, gadj.counit_naturality_assoc]
  rw [reassoc_of% (hc _), hsp]
  have hn := pullG.inv.naturality (adjG.projectionMorphism A K)
  dsimp at hn
  rw [reassoc_of% hn, ← rZ.map_comp_assoc, projectionMorphism, map_homEquiv_comp_counit]
  have hm := muZ.hom.naturality (Prod.mkHom (adjG.counit.app A) (𝟙 (Lg.obj K)))
  dsimp at hm
  simp only [MonoidalCategory.whiskerLeft_id, Category.comp_id] at hm
  have hs := spG.hom.naturality (Prod.mkHom (pS.app A) (𝟙 (rY.obj K)))
  dsimp at hs
  rw [rZ.map_comp_assoc, reassoc_of% hm, reassoc_of% (h' _ _), reassoc_of% hs]
  simp only [← TZ.map_comp, prod_comp, Category.assoc, hc, Functor.map_id, Category.id_comp,
    Category.comp_id, Iso.inv_hom_id_app]
  rfl

end ProperSquare

section OpenSquare

variable {AX AZ : Type u₁} {SX SZ : Type u₂} [Category.{v₁} AX] [Category.{v₁} AZ]
  [Category.{v₂} SX] [Category.{v₂} SZ]
  [MonoidalCategory AX] [MonoidalCategory AZ]
  {TX : SX × SX ⥤ SX} {TZ : SZ × SZ ⥤ SZ} {rX : AX ⥤ SX} {rZ : AZ ⥤ SZ}
  (muX : Functor.uncurry.obj (curriedTensor AX) ⋙ rX ≅ (rX.prod rX) ⋙ TX)
  (muZ : Functor.uncurry.obj (curriedTensor AZ) ⋙ rZ ≅ (rZ.prod rZ) ⋙ TZ)
  {I : AX ⥤ AZ} {Li : AZ ⥤ AX} (adjI : I ⊣ Li) [Li.Monoidal]
  {J : SX ⥤ SZ} {Gi : SZ ⥤ SX} (jadj : J ⊣ Gi)
  (spI : TZ ⋙ Gi ≅ (Gi.prod Gi) ⋙ TX) (pullI : Li ⋙ rX ≅ rZ ⋙ Gi)
  (oS : I ⋙ rZ ≅ rX ⋙ J)

/-- The transpose along `J ⊣ Gi` of `unit ⊗ id` followed by the inverse tensor comparison:
the inverse open projection map `J (B ⊠ Gi C) ⟶ J B ⊠ C`. -/
def unitTensorTranspose (B : SX) (C : SZ) :
    J.obj (TX.obj (B, Gi.obj C)) ⟶ TZ.obj (J.obj B, C) :=
  (jadj.homEquiv _ _).symm
    (TX.map (Prod.mkHom (jadj.unit.app B) (𝟙 (Gi.obj C))) ≫ spI.inv.app (J.obj B, C))

/-- `unitTensorTranspose` is natural in its second variable. -/
@[reassoc]
lemma unitTensorTranspose_naturality (B : SX) {C C' : SZ} (φ : C ⟶ C') :
    unitTensorTranspose jadj spI B C ≫ TZ.map (Prod.mkHom (𝟙 (J.obj B)) φ) =
      J.map (TX.map (Prod.mkHom (𝟙 B) (Gi.map φ))) ≫ unitTensorTranspose jadj spI B C' := by
  rw [unitTensorTranspose, unitTensorTranspose, ← homEquiv_naturality_right_symm,
    ← homEquiv_naturality_left_symm]
  congr 1
  have hs := spI.inv.naturality (Prod.mkHom (𝟙 (J.obj B)) φ)
  dsimp at hs
  rw [Category.assoc, ← hs, ← TX.map_comp_assoc, ← TX.map_comp_assoc]
  simp

/-- The open reduction square: if the reduction comparison `pullI` is compatible with the
monoidal structure of `Li` and the tensor comparisons, and `oS` is the inverse mate of
`pullI`, then the reduction of the inverse projection comparison of `I ⊣ Li`, transported
along `oS`, is the inverse of the transpose of `unit ⊗ id` along `J ⊣ Gi`. -/
theorem projectionComparison_reduction_square
    (h : ∀ A B : AZ, rX.map (Functor.OplaxMonoidal.δ Li A B) ≫ muX.hom.app (Li.obj A, Li.obj B) ≫
      TX.map (Prod.mkHom (pullI.hom.app A) (pullI.hom.app B)) =
      pullI.hom.app (A ⊗ B) ≫ Gi.map (muZ.hom.app (A, B)) ≫
        spI.hom.app (rZ.obj A, rZ.obj B))
    (hoS : oS.inv = ((mateEquiv adjI jadj).symm (TwoSquare.mk _ _ _ _ pullI.hom)).natTrans)
    (M : AX) (N : AZ) [IsIso (adjI.projectionComparison M N)] :
    rZ.map (inv (adjI.projectionComparison M N)) ≫ oS.hom.app (M ⊗ Li.obj N) ≫
        J.map (muX.hom.app (M, Li.obj N) ≫ TX.map (Prod.mkHom (𝟙 _) (pullI.hom.app N))) ≫
        unitTensorTranspose jadj spI (rX.obj M) (rZ.obj N) =
      muZ.hom.app (I.obj M, N) ≫ TZ.map (Prod.mkHom (oS.hom.app M) (𝟙 _)) := by
  have hu (B : AX) : rX.map (adjI.unit.app B) ≫ pullI.hom.app (I.obj B) =
      jadj.unit.app (rX.obj B) ≫ Gi.map (oS.inv.app B) := by
    rw [hoS]
    exact unit_mateEquiv_symm adjI jadj (TwoSquare.mk _ _ _ _ pullI.hom) B
  have h' (A B : AZ) : rX.map (Functor.LaxMonoidal.μ Li A B) ≫ pullI.hom.app (A ⊗ B) ≫
      Gi.map (muZ.hom.app (A, B)) =
      muX.hom.app (Li.obj A, Li.obj B) ≫ TX.map (Prod.mkHom (pullI.hom.app A) (pullI.hom.app B)) ≫
        spI.inv.app (rZ.obj A, rZ.obj B) := by
    rw [← cancel_mono (spI.hom.app (rZ.obj A, rZ.obj B))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← h A B, ← rX.map_comp_assoc, Functor.Monoidal.μ_δ, rX.map_id, Category.id_comp]
    simp
  rw [Functor.map_inv, IsIso.inv_comp_eq, ← cancel_epi (oS.inv.app _), Iso.inv_hom_id_app_assoc]
  apply (jadj.homEquiv _ _).injective
  rw [unitTensorTranspose]
  erw [homEquiv_naturality_left, Equiv.apply_symm_apply]
  rw [homEquiv_unit]
  simp only [Functor.map_comp]
  rw [← reassoc_of% (hu _)]
  have hn := pullI.hom.naturality (adjI.projectionComparison M N)
  dsimp at hn
  have hq : adjI.unit.app (M ⊗ Li.obj N) ≫ Li.map (adjI.projectionComparison M N) =
      adjI.unit.app M ▷ Li.obj N ≫ Functor.LaxMonoidal.μ Li (I.obj M) N := by
    refine (adjI.homEquiv_unit _ _ _).symm.trans ?_
    rw [projectionComparison]
    exact Equiv.apply_symm_apply _ _
  rw [← reassoc_of% hn, ← rX.map_comp_assoc, hq, rX.map_comp_assoc, reassoc_of% (h' _ _)]
  have hm := muX.hom.naturality (Prod.mkHom (adjI.unit.app M) (𝟙 (Li.obj N)))
  dsimp at hm
  simp only [MonoidalCategory.whiskerLeft_id, Category.comp_id] at hm
  have hs := spI.inv.naturality (Prod.mkHom (oS.hom.app M) (𝟙 (rZ.obj N)))
  dsimp at hs
  simp only [Category.assoc]
  rw [reassoc_of% hm, ← hs]
  simp only [← TX.map_comp_assoc, prod_comp, reassoc_of% (hu M), ← Gi.map_comp,
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp, Category.comp_id]
  simp

end OpenSquare

section CompactificationSquare

variable {AX AZ AY : Type u₁} {SX SZ SY : Type u₂} [Category.{v₁} AX] [Category.{v₁} AZ]
  [Category.{v₁} AY] [Category.{v₂} SX] [Category.{v₂} SZ] [Category.{v₂} SY]
  [MonoidalCategory AX] [MonoidalCategory AZ] [MonoidalCategory AY]
  {TX : SX × SX ⥤ SX} {TZ : SZ × SZ ⥤ SZ} {TY : SY × SY ⥤ SY}
  {rX : AX ⥤ SX} {rZ : AZ ⥤ SZ} {rY : AY ⥤ SY}
  (muX : Functor.uncurry.obj (curriedTensor AX) ⋙ rX ≅ (rX.prod rX) ⋙ TX)
  (muZ : Functor.uncurry.obj (curriedTensor AZ) ⋙ rZ ≅ (rZ.prod rZ) ⋙ TZ)
  (muY : Functor.uncurry.obj (curriedTensor AY) ⋙ rY ≅ (rY.prod rY) ⋙ TY)
  {I : AX ⥤ AZ} {Li : AZ ⥤ AX} (adjI : I ⊣ Li) [Li.Monoidal]
  {Lg : AY ⥤ AZ} {Rg : AZ ⥤ AY} (adjG : Lg ⊣ Rg) [Lg.Monoidal]
  {Lf : AY ⥤ AX}
  {J : SX ⥤ SZ} {Gi : SZ ⥤ SX} (jadj : J ⊣ Gi)
  {Gg : SY ⥤ SZ} {Pg : SZ ⥤ SY} (gadj : Gg ⊣ Pg) {Gf : SY ⥤ SX}
  (γ : ∀ C : SY, Gi.obj (Gg.obj C) ⟶ Gf.obj C)
  (spI : TZ ⋙ Gi ≅ (Gi.prod Gi) ⋙ TX) (spG : TY ⋙ Gg ≅ (Gg.prod Gg) ⋙ TZ)
  (pullI : Li ⋙ rX ≅ rZ ⋙ Gi) (pullG : Lg ⋙ rZ ≅ rY ⋙ Gg) (pullF : Lf ⋙ rX ≅ rY ⋙ Gf)
  (oS : I ⋙ rZ ≅ rX ⋙ J)

/-- The compactification reduction square: pasting the proper square of `Lg ⊣ Rg` with the
open square of `I ⊣ Li`, the reduction of the compact-support projection morphism
`PF_g ≫ Rg (q_i⁻¹ ≫ I (M ◁ e⁻¹))`, transported along `pS ≫ Pg oS` with `pS` the mate of
`pullG`, is the system compact-support projection. -/
theorem compactification_projection_reduction_square_unbundled
    (hI : ∀ A B : AZ, rX.map (Functor.OplaxMonoidal.δ Li A B) ≫
      muX.hom.app (Li.obj A, Li.obj B) ≫
      TX.map (Prod.mkHom (pullI.hom.app A) (pullI.hom.app B)) =
      pullI.hom.app (A ⊗ B) ≫ Gi.map (muZ.hom.app (A, B)) ≫
        spI.hom.app (rZ.obj A, rZ.obj B))
    (hG : ∀ A B : AY, rZ.map (Functor.OplaxMonoidal.δ Lg A B) ≫
      muZ.hom.app (Lg.obj A, Lg.obj B) ≫
      TZ.map (Prod.mkHom (pullG.hom.app A) (pullG.hom.app B)) =
      pullG.hom.app (A ⊗ B) ≫ Gg.map (muY.hom.app (A, B)) ≫
        spG.hom.app (rY.obj A, rY.obj B))
    (hoS : oS.inv = ((mateEquiv adjI jadj).symm (TwoSquare.mk _ _ _ _ pullI.hom)).natTrans)
    (M : AX) (K : AY) [hq : IsIso (adjI.projectionComparison M (Lg.obj K))]
    [hs : IsIso (unitTensorTranspose jadj spI (rX.obj M) (Gg.obj (rY.obj K)))]
    (ε : (Lg ⋙ Li).obj K ⟶ Lf.obj K)
    (hF : rX.map ε ≫ pullF.hom.app K =
      pullI.hom.app (Lg.obj K) ≫ Gi.map (pullG.hom.app K) ≫ γ (rY.obj K))
    (ρM : rY.obj (Rg.obj (I.obj M)) ⟶ Pg.obj (J.obj (rX.obj M)))
    (hρM : ρM = (mateEquiv adjG gadj (TwoSquare.mk _ _ _ _ pullG.inv)).natTrans.app
      (I.obj M) ≫ Pg.map (oS.hom.app M))
    (ρH : rY.obj (Rg.obj (I.obj (M ⊗ Lf.obj K))) ⟶ Pg.obj (J.obj (rX.obj (M ⊗ Lf.obj K))))
    (hρH : ρH = (mateEquiv adjG gadj (TwoSquare.mk _ _ _ _ pullG.inv)).natTrans.app
      (I.obj (M ⊗ Lf.obj K)) ≫ Pg.map (oS.hom.app (M ⊗ Lf.obj K))) :
    rY.map (adjG.projectionMorphism (I.obj M) K ≫
        Rg.map (inv (adjI.projectionComparison M (Lg.obj K)) ≫
          I.map (MonoidalCategoryStruct.whiskerLeft (Y₁ := Li.obj (Lg.obj K)) M ε))) ≫
      ρH ≫
      Pg.map (J.map (muX.hom.app (M, Lf.obj K) ≫
        TX.map (Prod.mkHom (𝟙 _) (pullF.hom.app K)))) =
    muY.hom.app (Rg.obj (I.obj M), K) ≫
      TY.map (Prod.mkHom ρM (𝟙 _)) ≫
      ((gadj.rightAdjointProjectionMap (T_C := Functor.curryObj TZ) (T_D := Functor.curryObj TY)
          (Functor.curry.mapIso spG ≪≫ Functor.curryObjProdComp Gg Gg TZ).hom).app
          (J.obj (rX.obj M))).app (rY.obj K) ≫
      Pg.map (inv (unitTensorTranspose jadj spI (rX.obj M) (Gg.obj (rY.obj K))) ≫
        J.map (TX.map (Prod.mkHom (𝟙 _) (γ (rY.obj K))))) := by
  subst hρM hρH
  have hP := projectionMorphism_reduction_square muY muZ adjG gadj spG pullG hG (I.obj M) K
  have hO := projectionComparison_reduction_square muX muZ adjI jadj spI pullI oS hI hoS M
    (Lg.obj K)
  generalize (mateEquiv adjG gadj (TwoSquare.mk _ _ _ _ pullG.inv)).natTrans = pS at hP ⊢
  generalize gadj.rightAdjointProjectionMap (T_C := Functor.curryObj TZ)
      (T_D := Functor.curryObj TY)
      (Functor.curry.mapIso spG ≪≫ Functor.curryObjProdComp Gg Gg TZ).hom = sP at hP ⊢
  have hbr : rZ.map (inv (adjI.projectionComparison M (Lg.obj K)) ≫
      I.map (MonoidalCategoryStruct.whiskerLeft (Y₁ := Li.obj (Lg.obj K)) M ε)) ≫
      oS.hom.app (M ⊗ Lf.obj K) ≫ J.map (muX.hom.app (M, Lf.obj K) ≫
        TX.map (Prod.mkHom (𝟙 _) (pullF.hom.app K))) =
      (muZ.hom.app (I.obj M, Lg.obj K) ≫ TZ.map (Prod.mkHom (𝟙 _) (pullG.hom.app K))) ≫
        TZ.map (Prod.mkHom (oS.hom.app M) (𝟙 _)) ≫
        inv (unitTensorTranspose jadj spI (rX.obj M) (Gg.obj (rY.obj K))) ≫
        J.map (TX.map (Prod.mkHom (𝟙 _) (γ (rY.obj K)))) := by
    have ho := oS.hom.naturality
      (MonoidalCategoryStruct.whiskerLeft (Y₁ := Li.obj (Lg.obj K)) M ε)
    have hm := muX.hom.naturality (Prod.mkHom (𝟙 M) (ε))
    have hn := unitTensorTranspose_naturality jadj spI (rX.obj M) (pullG.hom.app K)
    dsimp at ho hm hn
    simp only [MonoidalCategory.id_whiskerRight, Category.id_comp, rX.map_id] at hm
    have hn' : J.map (TX.map (Prod.mkHom (𝟙 (rX.obj M)) (Gi.map (pullG.hom.app K)))) =
        unitTensorTranspose jadj spI (rX.obj M) (rZ.obj (Lg.obj K)) ≫
          TZ.map (Prod.mkHom (𝟙 (J.obj (rX.obj M))) (pullG.hom.app K)) ≫
          inv (unitTensorTranspose jadj spI (rX.obj M) (Gg.obj (rY.obj K))) := by
      rw [reassoc_of% hn, IsIso.hom_inv_id, Category.comp_id]
    have hsplit : Prod.mkHom (𝟙 (rX.obj M))
        (rX.map ε ≫ pullF.hom.app K) =
        Prod.mkHom (𝟙 (rX.obj M)) (pullI.hom.app (Lg.obj K)) ≫
          Prod.mkHom (𝟙 (rX.obj M)) (Gi.map (pullG.hom.app K)) ≫
          Prod.mkHom (𝟙 (rX.obj M)) (γ (rY.obj K)) := by
      simp [hF]
    rw [rZ.map_comp, Category.assoc, reassoc_of% ho, ← J.map_comp, reassoc_of% hm,
      ← TX.map_comp]
    simp only [prod_comp, Category.id_comp]
    rw [hsplit]
    simp only [TX.map_comp, J.map_comp, Category.assoc]
    rw [hn']
    simp only [Category.assoc]
    rw [← J.map_comp_assoc, reassoc_of% hO]
    simp only [← TZ.map_comp_assoc, prod_comp, Category.id_comp, Category.comp_id]
  have hpn := pS.naturality (inv (adjI.projectionComparison M (Lg.obj K)) ≫
    I.map (MonoidalCategoryStruct.whiskerLeft (Y₁ := Li.obj (Lg.obj K)) M ε))
  have hsn : TY.map (Prod.mkHom (Pg.map (oS.hom.app M)) (𝟙 (rY.obj K))) ≫
      (sP.app (J.obj (rX.obj M))).app (rY.obj K) =
      (sP.app (rZ.obj (I.obj M))).app (rY.obj K) ≫
        Pg.map (TZ.map (Prod.mkHom (oS.hom.app M) (𝟙 (Gg.obj (rY.obj K))))) :=
    congrArg (fun φ ↦ φ.app (rY.obj K)) (sP.naturality (oS.hom.app M))
  dsimp at hpn
  rw [rY.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hpn]
  simp only [← Pg.map_comp]
  rw [hbr, Pg.map_comp, reassoc_of% hP]
  have hsplit : Prod.mkHom (pS.app (I.obj M) ≫ Pg.map (oS.hom.app M)) (𝟙 (rY.obj K)) =
      Prod.mkHom (pS.app (I.obj M)) (𝟙 (rY.obj K)) ≫
        Prod.mkHom (Pg.map (oS.hom.app M)) (𝟙 (rY.obj K)) := by
    simp
  rw [hsplit, TY.map_comp_assoc, reassoc_of% hsn, ← Pg.map_comp]
  rfl



/-- The compactification reduction square, with the compact-support projection morphism `Φ`,
the reconstruction maps `ρM`, `ρH` and the system projection `σ` given as morphisms between the
composite functors `I ⋙ Rg` and `J ⋙ Pg`, determined by their defining equations. -/
theorem compactification_projection_reduction_square
    (hI : ∀ A B : AZ, rX.map (Functor.OplaxMonoidal.δ Li A B) ≫
      muX.hom.app (Li.obj A, Li.obj B) ≫
      TX.map (Prod.mkHom (pullI.hom.app A) (pullI.hom.app B)) =
      pullI.hom.app (A ⊗ B) ≫ Gi.map (muZ.hom.app (A, B)) ≫
        spI.hom.app (rZ.obj A, rZ.obj B))
    (hG : ∀ A B : AY, rZ.map (Functor.OplaxMonoidal.δ Lg A B) ≫
      muZ.hom.app (Lg.obj A, Lg.obj B) ≫
      TZ.map (Prod.mkHom (pullG.hom.app A) (pullG.hom.app B)) =
      pullG.hom.app (A ⊗ B) ≫ Gg.map (muY.hom.app (A, B)) ≫
        spG.hom.app (rY.obj A, rY.obj B))
    (hoS : oS.inv = ((mateEquiv adjI jadj).symm (TwoSquare.mk _ _ _ _ pullI.hom)).natTrans)
    (M : AX) (K : AY) [hq : IsIso (adjI.projectionComparison M (Lg.obj K))]
    [hs : IsIso (unitTensorTranspose jadj spI (rX.obj M) (Gg.obj (rY.obj K)))]
    (ε : (Lg ⋙ Li).obj K ⟶ Lf.obj K)
    (hF : rX.map ε ≫ pullF.hom.app K =
      pullI.hom.app (Lg.obj K) ≫ Gi.map (pullG.hom.app K) ≫ γ (rY.obj K))
    (Φ : (I ⋙ Rg).obj M ⊗ K ⟶ (I ⋙ Rg).obj (M ⊗ Lf.obj K))
    (hΦ : Φ = adjG.projectionMorphism (I.obj M) K ≫
      Rg.map (inv (adjI.projectionComparison M (Lg.obj K)) ≫
        I.map (MonoidalCategoryStruct.whiskerLeft (Y₁ := Li.obj (Lg.obj K)) M ε)))
    (ρM : rY.obj ((I ⋙ Rg).obj M) ⟶ (J ⋙ Pg).obj (rX.obj M))
    (hρM : ρM = (mateEquiv adjG gadj (TwoSquare.mk _ _ _ _ pullG.inv)).natTrans.app
      (I.obj M) ≫ Pg.map (oS.hom.app M))
    (ρH : rY.obj ((I ⋙ Rg).obj (M ⊗ Lf.obj K)) ⟶ (J ⋙ Pg).obj (rX.obj (M ⊗ Lf.obj K)))
    (hρH : ρH = (mateEquiv adjG gadj (TwoSquare.mk _ _ _ _ pullG.inv)).natTrans.app
      (I.obj (M ⊗ Lf.obj K)) ≫ Pg.map (oS.hom.app (M ⊗ Lf.obj K)))
    (σ : TY.obj ((J ⋙ Pg).obj (rX.obj M), rY.obj K) ⟶
      (J ⋙ Pg).obj (TX.obj (rX.obj M, Gf.obj (rY.obj K))))
    (hσ : σ = ((gadj.rightAdjointProjectionMap (T_C := Functor.curryObj TZ)
        (T_D := Functor.curryObj TY)
        (Functor.curry.mapIso spG ≪≫ Functor.curryObjProdComp Gg Gg TZ).hom).app
          (J.obj (rX.obj M))).app (rY.obj K) ≫
      Pg.map (inv (unitTensorTranspose jadj spI (rX.obj M) (Gg.obj (rY.obj K))) ≫
        J.map (TX.map (Prod.mkHom (𝟙 _) (γ (rY.obj K)))))) :
    rY.map Φ ≫ ρH ≫ (J ⋙ Pg).map (muX.hom.app (M, Lf.obj K) ≫
        TX.map (Prod.mkHom (𝟙 _) (pullF.hom.app K))) =
      muY.hom.app ((I ⋙ Rg).obj M, K) ≫ TY.map (Prod.mkHom ρM (𝟙 _)) ≫ σ := by
  subst hΦ hσ
  exact compactification_projection_reduction_square_unbundled muX muZ muY adjI adjG jadj gadj
    γ spI spG pullI pullG pullF oS hI hG hoS M K ε hF ρM hρM ρH hρH

end CompactificationSquare

section Reconstruction

variable {AX AZ AY : Type u₁} {SX SZ SY : Type u₂} [Category.{v₁} AX] [Category.{v₁} AZ]
  [Category.{v₁} AY] [Category.{v₂} SX] [Category.{v₂} SZ] [Category.{v₂} SY]
  {rX : AX ⥤ SX} {rZ : AZ ⥤ SZ} {rY : AY ⥤ SY}
  {limX : SX ⥤ AX} {limZ : SZ ⥤ AZ} {limY : SY ⥤ AY}

/-- The counit transpose of the compactification/limit comparison
`Rg I (unit) ≫ Rg (open/limit) ≫ proper/limit` is the proper scalar comparison followed by
the proper image of the open scalar comparison. This uses only naturality and the triangle
identity of `rX ⊣ limX`. -/
theorem map_compactificationLimit_comp_counit (adjX : rX ⊣ limX) (adjZ : rZ ⊣ limZ)
    (adjY : rY ⊣ limY) {I : AX ⥤ AZ} {J : SX ⥤ SZ} {Rg : AZ ⥤ AY} {Pg : SZ ⥤ SY}
    (oS : I ⋙ rZ ≅ rX ⋙ J) (pS : Rg ⋙ rY ⟶ rZ ⋙ Pg) (N : AX) :
    rY.map (Rg.map (I.map (adjX.unit.app N)) ≫
        Rg.map (adjZ.homEquiv _ _ (oS.hom.app (limX.obj (rX.obj N)) ≫
          J.map (adjX.counit.app (rX.obj N)))) ≫
        adjY.homEquiv _ _ (pS.app (limZ.obj (J.obj (rX.obj N))) ≫
          Pg.map (adjZ.counit.app (J.obj (rX.obj N))))) ≫
      adjY.counit.app (Pg.obj (J.obj (rX.obj N))) =
    pS.app (I.obj N) ≫ Pg.map (oS.hom.app N) := by
  have hp := pS.naturality (I.map (adjX.unit.app N) ≫ adjZ.homEquiv _ _
    (oS.hom.app (limX.obj (rX.obj N)) ≫ J.map (adjX.counit.app (rX.obj N))))
  have ho := oS.hom.naturality (adjX.unit.app N)
  dsimp at hp ho
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [← Category.assoc, rY.map_comp, Category.assoc]
  erw [map_homEquiv_comp_counit]
  rw [← Rg.map_comp, reassoc_of% hp, ← Pg.map_comp, rZ.map_comp_assoc]
  erw [map_homEquiv_comp_counit]
  rw [reassoc_of% ho, ← J.map_comp, adjX.left_triangle_components, J.map_id, Category.comp_id]

end Reconstruction

section Transport

variable {ι : Type*} {A B S T : Type*} [Category* A] [Category* B] [Category* S]
  [Category* T]

/-- Transport of a family of comparisons `p a : L a ⋙ r ≅ r' ⋙ G a` along an equality of
indices followed by an isomorphism `e : L b ≅ H`. -/
lemma map_trans_inv_app_comp_hom_app {L : ι → A ⥤ B} {G : ι → S ⥤ T} {r : B ⥤ T}
    {r' : A ⥤ S} (p : ∀ a, L a ⋙ r ≅ r' ⋙ G a) {a b : ι} (h : a = b) {H : A ⥤ B}
    (e : L b ≅ H) (K : A) {Z₁ Z₂ : T} (x : r.obj (H.obj K) ⟶ Z₁) (y : Z₁ ⟶ Z₂)
    (z : Z₂ ⟶ (G b).obj (r'.obj K))
    (hb : r.map (e.inv.app K) ≫ (p b).hom.app K = x ≫ y ≫ z) :
    r.map ((eqToIso (congrArg L h) ≪≫ e).inv.app K) ≫ (p a).hom.app K =
      x ≫ y ≫ z ≫ eqToHom (congrArg (fun c ↦ (G c).obj (r'.obj K)) h.symm) := by
  subst h
  simpa using hb

/-- Variant of `map_trans_inv_app_comp_hom_app` for an isomorphism `e` which is equal to the
transport along `h` followed by `e'`. -/
lemma map_inv_app_comp_hom_app_of_eq {L : ι → A ⥤ B} {G : ι → S ⥤ T} {r : B ⥤ T}
    {r' : A ⥤ S} (p : ∀ a, L a ⋙ r ≅ r' ⋙ G a) {a b : ι} (h : a = b) {H : A ⥤ B}
    (e' : L b ≅ H) (e : L a ≅ H) (he : e = eqToIso (congrArg L h) ≪≫ e') (K : A) {Z₁ Z₂ : T}
    (x : r.obj (H.obj K) ⟶ Z₁) (y : Z₁ ⟶ Z₂) (z : Z₂ ⟶ (G b).obj (r'.obj K))
    (hb : r.map (e'.inv.app K) ≫ (p b).hom.app K = x ≫ y ≫ z) :
    r.map (e.inv.app K) ≫ (p a).hom.app K =
      x ≫ y ≫ z ≫ eqToHom (congrArg (fun c ↦ (G c).obj (r'.obj K)) h.symm) := by
  subst he
  exact map_trans_inv_app_comp_hom_app p h e' K x y z hb

end Transport

end CategoryTheory.Adjunction
