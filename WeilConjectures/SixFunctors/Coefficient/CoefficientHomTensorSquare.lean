/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomDomainCalculus

/-! # Evaluation comparisons through a tensor square

Source: blueprint `lem-coef-monoidal-square-hom-transport`, transpose argument,
written for the specified right tensor-Hom adjunctions.
-/

@[expose] public section
set_option autoImplicit false

universe a b c d va vb vc vd
open CategoryTheory Opposite
namespace WeilConjectures
open FiniteHomDomainClosedCalculus

attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
  CategoryTheory.uniformProd

private theorem comparison_evaluation
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (K M : A) :
    SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ K M) (𝟙 _)) ≫
        SB.evaluation (F.obj K) (F.obj M) =
      μ.inv.app (HA.obj (op K, M), K) ≫ F.map (SA.evaluation K M) := by
  exact (domainUncurry SB _ _ _ _).symm.trans
    (domainBaseChange_uncurry SA SB F μ K M)

private theorem comparison_composite_evaluation
    {A : Type a} {B : Type b} {C : Type c}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HC : Cᵒᵖ × C ⥤ C}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (F : A ⥤ B) (G : B ⥤ C)
    (μF : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (μG : SB.tensor ⋙ G ≅ G.prod G ⋙ SC.tensor) (K M : A) :
    SC.tensor.map (Prod.mkHom
        (G.map (coefficientBaseChangeHom SA SB F μF K M) ≫
          coefficientBaseChangeHom SB SC G μG (F.obj K) (F.obj M)) (𝟙 _)) ≫
        SC.evaluation (G.obj (F.obj K)) (G.obj (F.obj M)) =
      μG.inv.app (F.obj (HA.obj (op K, M)), F.obj K) ≫
        G.map (μF.inv.app (HA.obj (op K, M), K)) ≫
        G.map (F.map (SA.evaluation K M)) := by
  rw [← domainUncurry, domainUncurry_pre, domainBaseChange_uncurry]
  have hn := μG.inv.naturality
    (Prod.mkHom (coefficientBaseChangeHom SA SB F μF K M) (𝟙 (F.obj K)))
  simp only [Functor.comp_map, Functor.prod_map, G.map_id] at hn
  rw [← Category.assoc, hn, Category.assoc, ← G.map_comp,
    comparison_evaluation, G.map_comp]

/-- The canonical closed comparisons commute with a tensor-compatible square.
Only the tensor equation is needed; associativity and unit equations are separate.
Source: blueprint `lem-coef-monoidal-square-hom-transport`, evaluation transposition
(blueprint: lem-coef-right-closed-tensor-square).

Proof: uncurry both sides with the specified target adjunction, and precompose
with tensoring by the forward component on K. Naturality of the tensorators and
the counit identifies each composite comparison with the image of evaluation.
The tensor-square equation identifies their tensorators. Naturality of h at
evaluation identifies the remaining arrows. The inverse and forward components
on K cancel, and injectivity of the adjunction gives the assertion. -/
theorem coefficientHomTensorSquare
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    (μF : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (μG : SC.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (μU : SA.tensor ⋙ U ≅ U.prod U ⋙ SC.tensor)
    (μV : SB.tensor ⋙ V ≅ V.prod V ⋙ SD.tensor)
    (h : F ⋙ V ≅ U ⋙ G)
    (ht : ∀ K M : A,
      h.hom.app (SA.tensor.obj (K, M)) ≫ G.map (μU.hom.app (K, M)) ≫
          μG.hom.app (U.obj K, U.obj M) =
        V.map (μF.hom.app (K, M)) ≫ μV.hom.app (F.obj K, F.obj M) ≫
          SD.tensor.map (Prod.mkHom (h.hom.app K) (h.hom.app M)))
    (K M : A) :
    h.hom.app (HA.obj (op K, M)) ≫
        G.map (coefficientBaseChangeHom SA SC U μU K M) ≫
        coefficientBaseChangeHom SC SD G μG (U.obj K) (U.obj M) =
      V.map (coefficientBaseChangeHom SA SB F μF K M) ≫
        coefficientBaseChangeHom SB SD V μV (F.obj K) (F.obj M) ≫
        HD.map (Prod.mkHom (h.inv.app K).op (h.hom.app M)) := by
  apply (SD.transpose _ (G.obj (U.obj K)) (G.obj (U.obj M))).symm.injective
  rw [domainUncurry_pre]
  rw [← Category.assoc (V.map (coefficientBaseChangeHom SA SB F μF K M))
    (coefficientBaseChangeHom SB SD V μV (F.obj K) (F.obj M))
    (HD.map (Prod.mkHom (h.inv.app K).op (h.hom.app M))), domainUncurry_post]
  simp only [domainUncurry]
  rw [comparison_composite_evaluation, comparison_composite_evaluation]
  let H := HA.obj (op K, M)
  have hi : SD.tensor.map (Prod.mkHom (h.hom.app H) (h.hom.app K)) ≫
        μG.inv.app (U.obj H, U.obj K) ≫ G.map (μU.inv.app (H, K)) =
      μV.inv.app (F.obj H, F.obj K) ≫ V.map (μF.inv.app (H, K)) ≫
        h.hom.app (SA.tensor.obj (H, K)) := by
    let a := V.mapIso (μF.app (H, K))
    let b := μV.app (F.obj H, F.obj K)
    let c := G.mapIso (μU.app (H, K))
    let d := μG.app (U.obj H, U.obj K)
    have he : h.hom.app (SA.tensor.obj (H, K)) ≫ c.hom ≫ d.hom =
        a.hom ≫ b.hom ≫ SD.tensor.map (Prod.mkHom (h.hom.app H) (h.hom.app K)) :=
      ht H K
    change _ ≫ d.inv ≫ c.inv = b.inv ≫ a.inv ≫ _
    apply (cancel_epi b.hom).1
    apply (cancel_epi a.hom).1
    simp only [Iso.hom_inv_id_assoc]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
      using congrArg (fun f ↦ f ≫ d.inv ≫ c.inv) he.symm
  let e := SD.tensor.mapIso (Iso.prod (Iso.refl (V.obj (F.obj H))) (h.app K))
  apply (cancel_epi e.hom).1
  change SD.tensor.map (Prod.mkHom (𝟙 _) (h.hom.app K)) ≫ _ =
    SD.tensor.map (Prod.mkHom (𝟙 _) (h.hom.app K)) ≫ _
  simp only [← Category.assoc, ← SD.tensor.map_comp]
  simp only [CategoryTheory.prod_comp, Category.id_comp,
    Iso.hom_inv_id_app]
  simp only [Category.assoc]
  have hid : Prod.mkHom (𝟙 ((F ⋙ V).obj H)) (𝟙 ((F ⋙ V).obj K)) =
      𝟙 ((F ⋙ V).obj H, (F ⋙ V).obj K) := rfl
  rw [hid]
  erw [SD.tensor.map_id, Category.id_comp]
  erw [Category.comp_id (h.hom.app K)]
  have hi' := congrArg (fun f ↦ f ≫ G.map (U.map (SA.evaluation K M))) hi
  have hn := h.hom.naturality (SA.evaluation K M)
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc] at hi'
  erw [← hn] at hi'
  exact hi'

end WeilConjectures
