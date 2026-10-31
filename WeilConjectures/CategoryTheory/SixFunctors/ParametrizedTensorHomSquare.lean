/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Tensor comparison squares with explicitly supplied Hom adjunctions -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory Opposite
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : Type u₄} [Category.{v₄} J]
  {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D}
  {TE : E ⥤ E ⥤ E} {TJ : J ⥤ J ⥤ J}
  {HC : Cᵒᵖ ⥤ C ⥤ C} {HD : Dᵒᵖ ⥤ D ⥤ D}
  {HE : Eᵒᵖ ⥤ E ⥤ E} {HJ : Jᵒᵖ ⥤ J ⥤ J}

/-- Evaluation comparison using the supplied, rather than inferred, Hom adjunction.
Source: tensor--Hom adjunction, Stacks 07A4.
(blueprint: lem-sf-parametrized-tensor-hom-square). -/
def paramTensorComparisonHom (aC : TC ⊣₂ HC)
    (aD : TD ⊣₂ HD) (F : C ⥤ D)
    (t : Functor.uncurry.obj TC ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj TD) (K M : C) :
    F.obj ((HC.obj (op K)).obj M) ⟶ (HD.obj (op (F.obj K))).obj (F.obj M) :=
  (aD.adj (F.obj K)).homEquiv _ _
    (t.inv.app (K, (HC.obj (op K)).obj M) ≫ F.map ((aC.adj K).counit.app M))

private theorem comparison_comp
    (aC : TC ⊣₂ HC) (aD : TD ⊣₂ HD)
    (aE : TE ⊣₂ HE) (F : C ⥤ D) (G : D ⥤ E)
    (t : Functor.uncurry.obj TC ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj TD)
    (s : Functor.uncurry.obj TD ⋙ G ≅
      G.prod G ⋙ Functor.uncurry.obj TE) (K M : C) :
    (aE.homEquiv (X₁ := G.obj (F.obj K))).symm
      (G.map (paramTensorComparisonHom aC aD F t K M) ≫
        paramTensorComparisonHom aD aE G s (F.obj K) (F.obj M)) =
      s.inv.app (F.obj K, F.obj ((HC.obj (op K)).obj M)) ≫
        G.map (t.inv.app (K, (HC.obj (op K)).obj M)) ≫
        G.map (F.map ((aC.adj K).counit.app M)) := by
  rw [aE.homEquiv_symm_naturality_two]
  simp only [paramTensorComparisonHom, ← ParametrizedAdjunction.homEquiv_eq,
    Equiv.symm_apply_apply]
  have hn := s.inv.naturality
    (Prod.mkHom (𝟙 (F.obj K)) (paramTensorComparisonHom aC aD F t K M))
  simp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp] at hn
  change (TE.obj (G.obj (F.obj K))).map
      (G.map (paramTensorComparisonHom aC aD F t K M)) ≫
      s.inv.app (F.obj K, (HD.obj (op (F.obj K))).obj (F.obj M)) ≫
      G.map ((aD.adj (F.obj K)).counit.app (F.obj M)) = _
  rw [← Category.assoc, hn, Category.assoc, ← G.map_comp]
  have hev : (TD.obj (F.obj K)).map (paramTensorComparisonHom aC aD F t K M) ≫
      (aD.adj (F.obj K)).counit.app (F.obj M) =
      t.inv.app (K, (HC.obj (op K)).obj M) ≫
        F.map ((aC.adj K).counit.app M) := by
    exact ((aD.adj (F.obj K)).homEquiv _ _).symm_apply_apply _
  rw [hev, G.map_comp]

private theorem uncurry_map_second_first
    {V : Type*} [Category V] (T : V ⥤ V ⥤ V)
    {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y') :
    (Functor.uncurry.obj T).map (Prod.mkHom f g) =
      (T.obj X).map g ≫ (T.map f).app Y' := by
  exact ((T.map f).naturality g).symm

/-- A tensor square gives its internal-Hom square for any specified Hom adjunctions.
Source: blueprint coefficient extension proof, final paragraph.
(blueprint: lem-sf-parametrized-tensor-hom-square).
Proof: transpose the two paths by the supplied final adjunction. Naturality in
all three adjunction variables moves the contravariant and covariant input
comparisons outside. Naturality of the tensorators identifies the transpose of
each composite comparison. Substitute the tensor square at K and HC(K,M), then
use naturality of e at evaluation and cancel e with its inverse. -/
theorem paramTensorComparisonHom_square
    (aC : TC ⊣₂ HC) (aD : TD ⊣₂ HD)
    (aE : TE ⊣₂ HE) (aJ : TJ ⊣₂ HJ)
    (F : C ⥤ D) (G : E ⥤ J) (P : C ⥤ E) (Q : D ⥤ J)
    (tF : Functor.uncurry.obj TC ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj TD)
    (tG : Functor.uncurry.obj TE ⋙ G ≅
      G.prod G ⋙ Functor.uncurry.obj TJ)
    (tP : Functor.uncurry.obj TC ⋙ P ≅
      P.prod P ⋙ Functor.uncurry.obj TE)
    (tQ : Functor.uncurry.obj TD ⋙ Q ≅
      Q.prod Q ⋙ Functor.uncurry.obj TJ) (e : F ⋙ Q ≅ P ⋙ G)
    (ht : ∀ K L : C,
      (Functor.uncurry.obj TJ).map (Prod.mkHom (e.hom.app K) (e.hom.app L)) ≫
        tG.inv.app (P.obj K, P.obj L) ≫
          G.map (tP.inv.app (K, L)) =
        tQ.inv.app (F.obj K, F.obj L) ≫ Q.map (tF.inv.app (K, L)) ≫
          e.hom.app ((TC.obj K).obj L)) (K M : C) :
    G.map (paramTensorComparisonHom aC aE P tP K M) ≫
        paramTensorComparisonHom aE aJ G tG (P.obj K) (P.obj M) ≫
        (HJ.map (e.hom.app K).op).app (G.obj (P.obj M)) ≫
        (HJ.obj (op (Q.obj (F.obj K)))).map (e.inv.app M) =
      e.inv.app ((HC.obj (op K)).obj M) ≫
        Q.map (paramTensorComparisonHom aC aD F tF K M) ≫
        paramTensorComparisonHom aD aJ Q tQ (F.obj K) (F.obj M) := by
  apply (aJ.homEquiv (X₁ := Q.obj (F.obj K))).symm.injective
  simp only [← Category.assoc]
  rw [aJ.homEquiv_symm_naturality_three, aJ.homEquiv_symm_naturality_one]
  conv_rhs => rw [Category.assoc, aJ.homEquiv_symm_naturality_two]
  have hL := comparison_comp aC aE aJ P G tP tG K M
  have hR := comparison_comp aC aD aJ F Q tF tQ K M
  rw [hL]
  erw [hR]
  have he := e.hom.naturality ((aC.adj K).counit.app M)
  change Q.map (F.map ((aC.adj K).counit.app M)) ≫ e.hom.app M =
    e.hom.app ((TC.obj K).obj ((HC.obj (op K)).obj M)) ≫
      G.map (P.map ((aC.adj K).counit.app M)) at he
  have h := congrArg (fun z ↦ (TJ.obj (Q.obj (F.obj K))).map
      (e.inv.app ((HC.obj (op K)).obj M)) ≫ z ≫
      G.map (P.map ((aC.adj K).counit.app M)) ≫ e.inv.app M)
    (ht K ((HC.obj (op K)).obj M))
  simp only [Category.assoc] at h ⊢
  rw [← reassoc_of% he] at h
  dsimp only [Functor.comp_obj] at h
  simp only [Iso.hom_inv_id_app] at h
  simp only [uncurry_map_second_first, Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app] at h
  simpa only [Functor.comp_obj, Functor.map_id, Functor.map_comp, Category.assoc,
    Category.id_comp, Category.comp_id] using h

private theorem comparison_eq_of_evaluation
    (aC : TC ⊣₂ HC) (aD : TD ⊣₂ HD) (F : C ⥤ D)
    (t : Functor.uncurry.obj TC ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj TD)
    (c : ∀ K M : C, F.obj ((HC.obj (op K)).obj M) ⟶
      (HD.obj (op (F.obj K))).obj (F.obj M))
    (hc : ∀ K M : C,
      (TD.obj (F.obj K)).map (c K M) ≫ (aD.adj (F.obj K)).counit.app (F.obj M) =
        t.inv.app (K, (HC.obj (op K)).obj M) ≫ F.map ((aC.adj K).counit.app M))
    (K M : C) : c K M = paramTensorComparisonHom aC aD F t K M := by
  apply ((aD.adj (F.obj K)).homEquiv _ _).symm.injective
  rw [paramTensorComparisonHom, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact hc K M

/-- The tensor square also controls any Hom maps satisfying the evaluation equations.
Source: blueprint coefficient extension proof, final paragraph.
(blueprint: lem-sf-parametrized-tensor-hom-square).
Proof: injectivity of the inverse Hom equivalence identifies each supplied map
with the transpose of inverse tensorator followed by extended evaluation. Substitute
these four equalities in paramTensorComparisonHom_square. This formulation keeps
concrete derived adjunction structures out of the conversion of whole Hom maps. -/
theorem paramTensorComparisonHom_square_of_evaluation
    (aC : TC ⊣₂ HC) (aD : TD ⊣₂ HD)
    (aE : TE ⊣₂ HE) (aJ : TJ ⊣₂ HJ)
    (F : C ⥤ D) (G : E ⥤ J) (P : C ⥤ E) (Q : D ⥤ J)
    (tF : Functor.uncurry.obj TC ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj TD)
    (tG : Functor.uncurry.obj TE ⋙ G ≅
      G.prod G ⋙ Functor.uncurry.obj TJ)
    (tP : Functor.uncurry.obj TC ⋙ P ≅
      P.prod P ⋙ Functor.uncurry.obj TE)
    (tQ : Functor.uncurry.obj TD ⋙ Q ≅
      Q.prod Q ⋙ Functor.uncurry.obj TJ) (e : F ⋙ Q ≅ P ⋙ G)
    (cF : ∀ K M : C, F.obj ((HC.obj (op K)).obj M) ⟶
      (HD.obj (op (F.obj K))).obj (F.obj M))
    (cG : ∀ K M : E, G.obj ((HE.obj (op K)).obj M) ⟶
      (HJ.obj (op (G.obj K))).obj (G.obj M))
    (cP : ∀ K M : C, P.obj ((HC.obj (op K)).obj M) ⟶
      (HE.obj (op (P.obj K))).obj (P.obj M))
    (cQ : ∀ K M : D, Q.obj ((HD.obj (op K)).obj M) ⟶
      (HJ.obj (op (Q.obj K))).obj (Q.obj M))
    (hF : ∀ K M : C,
      (TD.obj (F.obj K)).map (cF K M) ≫ (aD.adj (F.obj K)).counit.app (F.obj M) =
        tF.inv.app (K, (HC.obj (op K)).obj M) ≫ F.map ((aC.adj K).counit.app M))
    (hG : ∀ K M : E,
      (TJ.obj (G.obj K)).map (cG K M) ≫ (aJ.adj (G.obj K)).counit.app (G.obj M) =
        tG.inv.app (K, (HE.obj (op K)).obj M) ≫ G.map ((aE.adj K).counit.app M))
    (hP : ∀ K M : C,
      (TE.obj (P.obj K)).map (cP K M) ≫ (aE.adj (P.obj K)).counit.app (P.obj M) =
        tP.inv.app (K, (HC.obj (op K)).obj M) ≫ P.map ((aC.adj K).counit.app M))
    (hQ : ∀ K M : D,
      (TJ.obj (Q.obj K)).map (cQ K M) ≫ (aJ.adj (Q.obj K)).counit.app (Q.obj M) =
        tQ.inv.app (K, (HD.obj (op K)).obj M) ≫ Q.map ((aD.adj K).counit.app M))
    (ht : ∀ K L : C,
      (Functor.uncurry.obj TJ).map (Prod.mkHom (e.hom.app K) (e.hom.app L)) ≫
        tG.inv.app (P.obj K, P.obj L) ≫ G.map (tP.inv.app (K, L)) =
      tQ.inv.app (F.obj K, F.obj L) ≫ Q.map (tF.inv.app (K, L)) ≫
        e.hom.app ((TC.obj K).obj L)) (K M : C) :
    G.map (cP K M) ≫ cG (P.obj K) (P.obj M) ≫
        (HJ.map (e.hom.app K).op).app (G.obj (P.obj M)) ≫
        (HJ.obj (op (Q.obj (F.obj K)))).map (e.inv.app M) =
      e.inv.app ((HC.obj (op K)).obj M) ≫ Q.map (cF K M) ≫ cQ (F.obj K) (F.obj M) := by
  have h := paramTensorComparisonHom_square aC aD aE aJ F G P Q tF tG tP tQ e ht K M
  simpa only [← comparison_eq_of_evaluation aC aD F tF cF hF,
    ← comparison_eq_of_evaluation aE aJ G tG cG hG,
    ← comparison_eq_of_evaluation aC aE P tP cP hP,
    ← comparison_eq_of_evaluation aD aJ Q tQ cQ hQ] using h

end CategoryTheory
