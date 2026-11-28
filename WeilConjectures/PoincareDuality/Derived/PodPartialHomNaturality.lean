/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationBase

/-! # Naturality of the evaluation-defined internal Hom comparison

If inverse transposition is natural in the permitted Hom pair on both sides and the tensor
comparison is natural in both variables, then the evaluation-defined comparison
`podPartialHomComparison` is natural on the permitted pairs.

## Main statements

* `podPartialHomComparison_naturality_of`: naturality of the evaluation-defined comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe a b c d
open CategoryTheory Opposite
namespace WeilConjectures

variable {C : Type a} {D : Type c}
  [Category.{b} C] [Category.{d} D] [Preadditive C] [Preadditive D]
  {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {J : ObjectProperty (Cᵒᵖ × C)} {K : ObjectProperty (Dᵒᵖ × D)}
  {HC : J.FullSubcategory ⥤ C} {HD : K.FullSubcategory ⥤ D}

/-- Inverse transposition turns precomposition with a parameter arrow into tensoring
with it. -/
theorem PodPartialClosed.symm_comp {T : C × C ⥤ C} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H) (L L' : C) (P : J.FullSubcategory) (f : L' ⟶ L)
    (g : L ⟶ H.obj P) :
    (S.transpose L' P).symm (f ≫ g) =
      T.map (Prod.mkHom f (𝟙 _)) ≫ (S.transpose L P).symm g := by
  apply (S.transpose L' P).injective
  rw [S.parameter_naturality, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The evaluation-defined comparison is natural on permitted pairs, provided inverse
transposition is natural in the Hom pair on both sides and the tensor comparison is
natural in both variables. -/
theorem podPartialHomComparison_naturality_of
    (SC : PodPartialClosed TC J HC) (SD : PodPartialClosed TD K HD)
    (F : C ⥤ D) (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj))
    (μ : ∀ L M : C, F.obj (TC.obj (L, M)) ≅ TD.obj (F.obj L, F.obj M))
    (hSC : ∀ (L : C) (P Q : J.FullSubcategory) (f : P ⟶ Q) (φ : L ⟶ HC.obj P),
      (SC.transpose L Q).symm (φ ≫ HC.map f) =
        TC.map (Prod.mkHom (𝟙 L) f.hom.1.unop) ≫ (SC.transpose L P).symm φ ≫ f.hom.2)
    (hSD : ∀ (L : D) (P Q : K.FullSubcategory) (f : P ⟶ Q) (φ : L ⟶ HD.obj P),
      (SD.transpose L Q).symm (φ ≫ HD.map f) =
        TD.map (Prod.mkHom (𝟙 L) f.hom.1.unop) ≫ (SD.transpose L P).symm φ ≫ f.hom.2)
    (hμ : ∀ (L L' M M' : C) (x : L' ⟶ L) (y : M' ⟶ M),
      TD.map (Prod.mkHom (F.map x) (F.map y)) ≫ (μ L M).inv =
        (μ L' M').inv ≫ F.map (TC.map (Prod.mkHom x y)))
    (P Q : J.FullSubcategory) (f : P ⟶ Q) :
    F.map (HC.map f) ≫ podPartialHomComparison SC SD F h μ Q =
      podPartialHomComparison SC SD F h μ P ≫ HD.map ((podPairPullback F J K h).map f) := by
  apply (SD.transpose _ ((podPairPullback F J K h).obj Q)).symm.injective
  rw [hSD, PodPartialClosed.symm_comp]
  dsimp only [podPartialHomComparison]
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  have hf : TC.map (Prod.mkHom (HC.map f) (𝟙 _)) ≫ SC.evaluation Q =
      TC.map (Prod.mkHom (𝟙 _) f.hom.1.unop) ≫ SC.evaluation P ≫ f.hom.2 := by
    have h₁ := SC.symm_comp _ _ Q (HC.map f) (𝟙 _)
    have h₂ := hSC _ P Q f (𝟙 _)
    rw [Category.comp_id] at h₁
    rw [Category.id_comp] at h₂
    exact h₁.symm.trans h₂
  have h₁ := hμ _ _ _ _ (HC.map f) (𝟙 Q.obj.1.unop)
  have h₂ := hμ _ _ _ _ (𝟙 (HC.obj P)) f.hom.1.unop
  rw [F.map_id] at h₁ h₂
  refine ((reassoc_of% h₁) (F.map (SC.evaluation Q))).trans ?_
  rw [← F.map_comp, hf, F.map_comp, F.map_comp]
  exact ((reassoc_of% h₂) (F.map (SC.evaluation P) ≫ F.map f.hom.2)).symm.trans
    (congrArg _ (Category.assoc _ _ _).symm)


/-- Transposition turns tensoring with a pair arrow and postcomposing with its second
component into postcomposition with its internal Hom, when inverse transposition is
natural in the Hom pair. -/
theorem PodPartialClosed.transpose_comp_map {T : C × C ⥤ C} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H)
    (hS : ∀ (L : C) (P Q : J.FullSubcategory) (f : P ⟶ Q) (φ : L ⟶ H.obj P),
      (S.transpose L Q).symm (φ ≫ H.map f) =
        T.map (Prod.mkHom (𝟙 L) f.hom.1.unop) ≫ (S.transpose L P).symm φ ≫ f.hom.2)
    (L : C) (P Q : J.FullSubcategory) (f : P ⟶ Q) (g : T.obj (L, P.obj.1.unop) ⟶ P.obj.2) :
    S.transpose L Q (T.map (Prod.mkHom (𝟙 L) f.hom.1.unop) ≫ g ≫ f.hom.2) =
      S.transpose L P g ≫ H.map f := by
  apply (S.transpose L Q).symm.injective
  rw [AddEquiv.symm_apply_apply, hS, AddEquiv.symm_apply_apply]

/-- The transpose of the evaluation-defined composite, transported along an isomorphism of
the parameter and an isomorphism of permitted pairs, is invertible as soon as the
evaluation-defined comparison is. -/
theorem podPartialHomComparison_transpose_isIso
    (SC : PodPartialClosed TC J HC) (SD : PodPartialClosed TD K HD)
    (F : C ⥤ D) (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj))
    (μ : ∀ L M : C, F.obj (TC.obj (L, M)) ≅ TD.obj (F.obj L, F.obj M))
    (hSD : ∀ (L : D) (P Q : K.FullSubcategory) (f : P ⟶ Q) (φ : L ⟶ HD.obj P),
      (SD.transpose L Q).symm (φ ≫ HD.map f) =
        TD.map (Prod.mkHom (𝟙 L) f.hom.1.unop) ≫ (SD.transpose L P).symm φ ≫ f.hom.2)
    (hμ : ∀ (L L' M : C) (t : L' ⟶ L),
      TD.map (Prod.mkHom (F.map t) (𝟙 _)) ≫ (μ L M).inv =
        (μ L' M).inv ≫ F.map (TC.map (Prod.mkHom t (𝟙 _))))
    (P : J.FullSubcategory) (A : C) (c : A ≅ HC.obj P) (XA : D) (a : XA ≅ F.obj A)
    (Q : K.FullSubcategory) (e : (podPairPullback F J K h).obj P ≅ Q)
    (hc : IsIso (podPartialHomComparison SC SD F h μ P)) :
    IsIso (SD.transpose XA Q (TD.map (Prod.mkHom a.hom e.hom.hom.1.unop) ≫
      (μ A P.obj.1.unop).inv ≫ F.map ((SC.transpose A P).symm c.hom) ≫ e.hom.hom.2)) := by
  have hm : Prod.mkHom a.hom e.hom.hom.1.unop =
      (Prod.mkHom a.hom (𝟙 _) : (XA, Q.obj.1.unop) ⟶ (F.obj A, Q.obj.1.unop)) ≫
        Prod.mkHom (𝟙 _) e.hom.hom.1.unop := by
    ext <;> simp
  have hev : (SC.transpose A P).symm c.hom =
      TC.map (Prod.mkHom c.hom (𝟙 _)) ≫ SC.evaluation P := by
    rw [PodPartialClosed.evaluation, ← PodPartialClosed.symm_comp, Category.comp_id]
  have key : SD.transpose XA Q (TD.map (Prod.mkHom a.hom e.hom.hom.1.unop) ≫
      (μ A P.obj.1.unop).inv ≫ F.map ((SC.transpose A P).symm c.hom) ≫ e.hom.hom.2) =
      a.hom ≫ F.map c.hom ≫ podPartialHomComparison SC SD F h μ P ≫ HD.map e.hom := by
    rw [hm, TD.map_comp, Category.assoc, SD.parameter_naturality]
    refine congrArg (a.hom ≫ ·) ((congrArg (SD.transpose _ Q) (congrArg (_ ≫ ·)
      (Category.assoc _ _ _).symm)).trans ((PodPartialClosed.transpose_comp_map SD hSD (F.obj A) _ Q
      e.hom ((μ A P.obj.1.unop).inv ≫ F.map ((SC.transpose A P).symm c.hom))).trans ?_))
    rw [hev, F.map_comp]
    refine (congrArg (· ≫ HD.map e.hom) ((congrArg (SD.transpose _ _)
      ((reassoc_of% (hμ (HC.obj P) A P.obj.1.unop c.hom)) (F.map (SC.evaluation P))).symm).trans
        ?_)).trans (Category.assoc _ _ _)
    exact SD.parameter_naturality _ _ _ _ _
  rw [key]
  infer_instance

end WeilConjectures
