/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralHomScalarTensorModelComparison

/-! # Invertibility of the finite-extension evaluation transpose

The finite-free calculation is already proved for the canonical closed models.
Transport its specified transpose through the normalized tensor-model comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b c d v
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace WeilConjectures.IntegralFiniteExtension
variable {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
  (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
  {F G : A ⥤ B} (e : F ≅ G)
  (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)

private def transportTensor : SA.tensor ⋙ G ≅ G.prod G ⋙ SB.tensor :=
  Functor.isoWhiskerLeft SA.tensor e.symm ≪≫ μ ≪≫
    Functor.isoWhiskerRight (NatIso.prod e e) SB.tensor

private theorem uncurry_naturality {A : Type c} [Category.{v} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H)
    (K K' L L' M M' : A) (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
    (f : K ⟶ H.obj (op L, M)) :
    (S.transpose K' L' M').symm (a ≫ f ≫ H.map (b.op, c)) =
      S.tensor.map (a, b) ≫ (S.transpose K L M).symm f ≫ c := by
  let := S.monoidal
  have hh : H.map (b.op, c) =
      H.map (X := (op L, M)) (Y := (op L', M)) (b.op, 𝟙 M) ≫
        H.map (X := (op L', M)) (Y := (op L', M')) (𝟙 (op L'), c) := by
    rw [← H.map_comp]
    simp
  dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor]
  rw [hh]
  erw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (S.adjunction L').counit.naturality c
  change (tensorRight L').map (H.map (X := (op L', M)) (Y := (op L', M')) (𝟙 (op L'), c)) ≫
    (S.adjunction L').counit.app M' = (S.adjunction L').counit.app M ≫ c at hn
  erw [hn]
  erw [reassoc_of% (S.evaluation_naturality L L' M b)]
  change (a ▷ L') ≫ (f ▷ L') ≫ (H.obj (op L, M) ◁ b) ≫
    (S.adjunction L).counit.app M ≫ c =
      (a ⊗ₘ b) ≫ (f ▷ L) ≫ (S.adjunction L).counit.app M ≫ c
  simp only [← tensorHom_id, ← id_tensorHom, ← Category.assoc,
    tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

private theorem transportHom (K M : A) :
    coefficientBaseChangeHom SA SB G (transportTensor SA SB e μ) K M =
      e.inv.app (HA.obj (op K, M)) ≫ coefficientBaseChangeHom SA SB F μ K M ≫
        HB.map (Prod.mkHom (e.inv.app K).op (e.hom.app M)) := by
  apply (SB.transpose _ (G.obj K) (G.obj M)).symm.injective
  dsimp only [coefficientBaseChangeHom]
  rw [Equiv.symm_apply_apply]
  rw [uncurry_naturality SB]
  dsimp only [coefficientBaseChangeHom]
  rw [Equiv.symm_apply_apply]
  dsimp only [transportTensor, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatIso.prod_inv, Iso.symm_inv]
  simp only [Category.assoc]
  rw [← e.hom.naturality]
  rfl

private theorem inverseSquare {C : Type*} [Category* C] {W X Y Z : C}
    (i : W ≅ X) (j : Y ≅ Z) (f : W ⟶ Y) (g : X ⟶ Z)
    (h : f ≫ j.hom = i.hom ≫ g) : i.inv ≫ f = g ≫ j.inv := by
  apply (cancel_epi i.hom).1
  rw [← Category.assoc, i.hom_inv_id, Category.id_comp]
  rw [← Category.assoc, ← h, Category.assoc, j.hom_inv_id, Category.comp_id]

private theorem leftAdjointHomEquiv {C : Type*} [Category* C]
    {D : Type*} [Category* D] {L L' : C ⥤ D} {R : D ⥤ C}
    (ad : L ⊣ R) (ad' : L' ⊣ R) (T : C) (M : D) (f : L'.obj T ⟶ M) :
    ad.homEquiv T M ((Adjunction.leftAdjointUniq ad ad').hom.app T ≫ f) =
      ad'.homEquiv T M f := by
  rw [ad.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit]

private theorem transposeComparison
    {A B : Type*} [Category* A] [Category* B]
    {LA LA' RA : A ⥤ A} {LB LB' RB : B ⥤ B}
    (adA : LA ⊣ RA) (adA' : LA' ⊣ RA)
    (adB : LB ⊣ RB) (adB' : LB' ⊣ RB) (F : A ⥤ B) (M : A)
    (f : LB.obj (F.obj (RA.obj M)) ⟶ F.obj (LA.obj (RA.obj M)))
    (g : LB'.obj (F.obj (RA.obj M)) ⟶ F.obj (LA'.obj (RA.obj M)))
    (h : f ≫ F.map ((Adjunction.leftAdjointUniq adA adA').hom.app (RA.obj M)) =
      (Adjunction.leftAdjointUniq adB adB').hom.app (F.obj (RA.obj M)) ≫ g) :
    adB.homEquiv _ _ (f ≫ F.map (adA.counit.app M)) =
      adB'.homEquiv _ _ (g ≫ F.map (adA'.counit.app M)) := by
  rw [← Adjunction.leftAdjointUniq_hom_app_counit adA adA' M,
    F.map_comp, ← Category.assoc, h, Category.assoc]
  exact leftAdjointHomEquiv adB adB' _ _ _

end WeilConjectures.IntegralFiniteExtension

universe u
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (a : IntegralHom.TensorPresentation.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X))
  (b : IntegralHom.TensorPresentation.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X))

variable (K M : IntegralVerdier.Ambient l E X)

/-- The evaluation transpose is an isomorphism by the finite-free basis calculation.
Source: finite-free basis calculation for the scalar-extended evaluation transpose.
The canonical ordinary comparison is invertible by scalarHomOrdinary_isIso.
The normalized tensor comparison identifies its mate with the supplied homMap;
transport along the scalar-model isomorphism and the adjunction comparisons
preserves invertibility. No completeness hypothesis on either input is used.
(blueprint: lem-sf-integral-finite-extension-hom-map-invertibility)
-/
theorem homMap_isIso :
    IsIso (homMap X (completedCoefficientMap l E L ι X) a b K M) := by
  obtain ⟨t, e, ht, he, _⟩ := integralScalarOrdinaryModelComparison l E L ι X
  have hn := scalarTensor_model_comparison l E L ι X a b t e ht he
  let SA := scalarIntegralClosed l E X
  let SB := scalarIntegralClosed l L X
  let G := pbcDerivedExtend (completedCoefficientMap l E L ι X)
  let eG : integralOrdinaryDerivedScalar l E L ι X ≅ G := e
  let μ := transportTensor SA SB eG (scalarClosedTensor l E L ι X)
  let μa := PurCompactSupport.scalarTensor (completedCoefficientMap l E L ι X)
    (tensorModel X a) (tensorModel X b)
  let H := (IntegralHom.hom.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M)
  let γa := Adjunction.leftAdjointUniq (a.adjunction K) (SA.adjunction K)
  let γb := Adjunction.leftAdjointUniq (b.adjunction (G.obj K)) (SB.adjunction (G.obj K))
  have hs : μa.inv.app (K, H) ≫ G.map (γa.hom.app H) =
      γb.hom.app (G.obj H) ≫ μ.inv.app (H, K) := by
    exact inverseSquare (μa.app (K, H)) (μ.app (H, K))
      (G.map (γa.hom.app H)) (γb.hom.app (G.obj H)) (hn K H)
  have hc : homMap X (completedCoefficientMap l E L ι X) a b K M =
      coefficientBaseChangeHom SA SB G μ K M := by
    exact transposeComparison (a.adjunction K) (SA.adjunction K)
      (b.adjunction (G.obj K)) (SB.adjunction (G.obj K)) G M
      (μa.inv.app (K, H)) (μ.inv.app (H, K)) hs
  rw [hc, transportHom SA SB eG]
  have := scalarHomOrdinary_isIso l E L ι X K M
  change IsIso (eG.inv.app H ≫ scalarHomOrdinary l E L ι X K M ≫
    (IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)).map
      (Prod.mkHom (eG.inv.app K).op (eG.hom.app M)))
  have : IsIso (Prod.mkHom (eG.inv.app K).op (eG.hom.app M)) := by
    refine ⟨⟨Prod.mkHom (eG.hom.app K).op (eG.inv.app M), ?_, ?_⟩⟩
    · ext <;> simp
    · ext <;> simp
  infer_instance
end WeilConjectures.IntegralFiniteExtension
