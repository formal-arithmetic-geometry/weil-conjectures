/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual

/-! # Canonical twist interchange in the recorded coefficient presentations

Source: main-20261015, sk-lem-sf-twist-interchange, proof paragraphs 1--3
(blueprint: sk-lem-sf-twist-interchange).
The existing ordinary-etale specialization remains publicly imported.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b
open CategoryTheory Opposite
namespace WeilConjectures

/-- The comparison is the transpose of evaluation tensored with the identity, with the
specified signed symmetry. Source: twist-interchange proof paragraph 1
(blueprint: sk-lem-sf-twist-interchange). -/
def sfTwistTensorHomMap {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (s : @SymmetricCategory B _ S.monoidal)
    (P M T : B) : S.tensor.obj (H.obj (op P, M), T) ⟶
      H.obj (op P, S.tensor.obj (M, T)) :=
  S.transpose _ P _
    ((S.monoidal.associator _ T P).hom ≫
      S.tensor.map (Prod.mkHom (𝟙 _) (s.braiding T P).hom) ≫
      (S.monoidal.associator _ P T).inv ≫
      S.tensor.map (Prod.mkHom (S.evaluation P M) (𝟙 T)))

/-- The evaluation-defined twist comparison is invertible for perfect P and an
invertible T. Source: twist-interchange proof paragraphs 1--3
(blueprint: sk-lem-sf-twist-interchange).
Proof: tensoring with T is an autoequivalence with quasi-inverse tensoring with
its inverse line. The tensor-Hom adjunctions therefore identify maps into both
sides. Following the identity through these bijections gives precisely the
transpose of evaluation tensored with identity, namely sfTwistTensorHomMap.
Yoneda makes this map invertible. Equivalently, for dualizable P identify both
Homs with tensor by its coefficient dual and use the associator. -/
theorem sfTwistTensorHomMap_isIso {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (s : @SymmetricCategory B _ S.monoidal)
    (P M T : B) (hP : @IsDualizable B _ S.monoidal P)
    (hT : @IsInvertible B _ S.monoidal T) : IsIso (sfTwistTensorHomMap S s P M T) := by
  -- Keep the perfect-object hypothesis; invertibility of the twist already suffices.
  obtain ⟨_⟩ := hP
  let : MonoidalCategory B := S.monoidal
  let : SymmetricCategory B := s
  -- Transport the recorded adjunction without changing the internal Hom.
  let : MonoidalClosed B :=
    { closed Q :=
        { rightAdj := Prod.sectR (op Q) B ⋙ H
          adj := (S.adjunction Q).ofNatIsoLeft
            (BraidedCategory.tensorLeftIsoTensorRight Q).symm } }
  -- Compare the two transposes using the hexagon and symmetry identities.
  open MonoidalCategory in
  have h : sfTwistTensorHomMap S s P M T =
      MonoidalClosed.ihomTensorToIhom P M T := by
    unfold sfTwistTensorHomMap MonoidalClosed.ihomTensorToIhom MonoidalClosed.curry
    change (S.adjunction P).homEquiv _ _ _ =
      ((S.adjunction P).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight P).symm).homEquiv _ _ _
    rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
    congr 1
    change (α_ (H.obj (op P, M)) T P).hom ≫
        ((𝟙 (H.obj (op P, M))) ⊗ₘ (β_ T P).hom) ≫ (α_ _ P T).inv ≫
          ((S.evaluation P M) ⊗ₘ (𝟙 T)) =
      (β_ P (H.obj (op P, M) ⊗ T)).inv ≫ (α_ P _ T).inv ≫
        ((β_ P (H.obj (op P, M))).hom ≫ S.evaluation P M) ▷ T
    simp only [id_tensorHom, tensorHom_id]
    rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
    simp only [BraidedCategory.braiding_tensor_left_hom, comp_whiskerRight,
      Category.assoc, Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight_assoc, SymmetricCategory.symmetry,
      id_whiskerRight, Category.id_comp]
  rw [h]
  exact MonoidalClosed.isIso_ihomTensorToIhom P M hT

/-- The canonical inverse comparison, retaining its evaluation normalization.
Source: twist-interchange proof paragraph 1
(blueprint: sk-lem-sf-twist-interchange). -/
def sfTwistTensorHomIso {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (s : @SymmetricCategory B _ S.monoidal)
    (P M T : B) (hP : @IsDualizable B _ S.monoidal P)
    (hT : @IsInvertible B _ S.monoidal T) :
    H.obj (op P, S.tensor.obj (M, T)) ≅ S.tensor.obj (H.obj (op P, M), T) :=
  haveI := sfTwistTensorHomMap_isIso S s P M T hP hT
  (asIso (sfTwistTensorHomMap S s P M T)).symm

/-- The unit case of canonical twist interchange, after the target unitor.
Source: twist-interchange proof final paragraph
(blueprint: sk-lem-sf-twist-interchange). -/
def sfCoefficientTwistIso {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (s : @SymmetricCategory B _ S.monoidal)
    (P T : B) (hP : @IsDualizable B _ S.monoidal P)
    (hT : @IsInvertible B _ S.monoidal T) :
    H.obj (op P, T) ≅ S.tensor.obj (H.obj (op P, S.monoidal.tensorUnit), T) :=
  H.mapIso (Iso.prod (Iso.refl (op P)) (S.monoidal.leftUnitor T).symm) ≪≫
    sfTwistTensorHomIso S s P S.monoidal.tensorUnit T hP hT

end WeilConjectures
