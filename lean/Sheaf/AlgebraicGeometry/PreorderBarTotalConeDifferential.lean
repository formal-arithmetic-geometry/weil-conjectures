/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.AlgebraicGeometry.PreorderBarTotalCone
import Sheaf.AlgebraicGeometry.PreorderBarTotalDifferential
import Sheaf.AlgebraicGeometry.PreorderBarTotalSplit
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! # The total-cone comparison commutes with differentials

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
attribute [local implicit_reducible] OrderHom.comp
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.PreorderBar
variable {I : Type u} [Preorder I] {A : Type w} [Category.{v} A] [Preadditive A]
  [HasBinaryBiproducts A] [HasCoproducts.{u} A] [HasCoproducts.{0} A]
  {D E : I ⥤ CochainComplex A ℤ} (φ : D ⟶ E)

omit [HasCoproducts.{u} A] [HasCoproducts.{0} A] in
@[reassoc (attr := simp)]
lemma inl_coneDiagram_map {i j : I} (g : i ⟶ j) (q : ℤ) :
    (CochainComplex.mappingCone.inl (φ.app i)).v (q + 1) q (by omega) ≫
      ((coneDiagram φ).map g).f q =
    (D.map g).f (q + 1) ≫
      (CochainComplex.mappingCone.inl (φ.app j)).v (q + 1) q (by omega) := by
  simp [coneDiagram, CochainComplex.mappingCone.map]

omit [HasCoproducts.{u} A] [HasCoproducts.{0} A] in
@[reassoc (attr := simp)]
lemma inr_coneDiagram_map {i j : I} (g : i ⟶ j) (q : ℤ) :
    (CochainComplex.mappingCone.inr (φ.app i)).f q ≫ ((coneDiagram φ).map g).f q =
      (E.map g).f q ≫ (CochainComplex.mappingCone.inr (φ.app j)).f q := by
  simp [coneDiagram, CochainComplex.mappingCone.map]

omit [HasBinaryBiproducts A] in
@[reassoc]
lemma ιTerm_totalArrow (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n)
    (σ : Fin (p + 1) →o I) :
    ιTerm D p q n h σ ≫ (totalArrow φ).f n =
      (φ.app (σ 0)).f q ≫ ιTerm E p q n h σ := by
  convert! ιTerm_map D E OrderHom.id (sameIndexMap φ) p q n h σ using 1

private lemma inl_face_XHom (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n)
    (σ : Fin (p + 2) →o I) (a : Fin (p + 2)) :
    (CochainComplex.mappingCone.inl (φ.app (σ 0))).v (q + 1) q (by omega) ≫
      ((coneDiagram φ).map (faceArrow σ a)).f q ≫
        ιTerm (coneDiagram φ) p q n h (σ.comp (SimplexCategory.δ a).toOrderHom) ≫
          coneTotalXHom φ n =
    ((-1 : ℤ) ^ p) • ((D.map (faceArrow σ a)).f (q + 1) ≫
      ιTerm D p (q + 1) (n + 1) (by omega) (σ.comp (SimplexCategory.δ a).toOrderHom) ≫
        (CochainComplex.mappingCone.inl (totalArrow φ)).v (n + 1) n (by omega)) := by
  rw [inl_coneDiagram_map_assoc]
  change (D.map (faceArrow σ a)).f (q + 1) ≫
    ((CochainComplex.mappingCone.inl
      (φ.app ((σ.comp (SimplexCategory.δ a).toOrderHom) 0))).v (q + 1) q (by omega) ≫
        ιTerm (coneDiagram φ) p q n h (σ.comp (SimplexCategory.δ a).toOrderHom) ≫
          coneTotalXHom φ n) = _
  rw [inl_ιTerm_coneTotalXHom, Preadditive.comp_zsmul]

private lemma inr_face_XHom (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n)
    (σ : Fin (p + 2) →o I) (a : Fin (p + 2)) :
    (CochainComplex.mappingCone.inr (φ.app (σ 0))).f q ≫
      ((coneDiagram φ).map (faceArrow σ a)).f q ≫
        ιTerm (coneDiagram φ) p q n h (σ.comp (SimplexCategory.δ a).toOrderHom) ≫
          coneTotalXHom φ n =
    (E.map (faceArrow σ a)).f q ≫
      ιTerm E p q n h (σ.comp (SimplexCategory.δ a).toOrderHom) ≫
        (CochainComplex.mappingCone.inr (totalArrow φ)).f n := by
  rw [inr_coneDiagram_map_assoc]
  change (E.map (faceArrow σ a)).f q ≫
    ((CochainComplex.mappingCone.inr
      (φ.app ((σ.comp (SimplexCategory.δ a).toOrderHom) 0))).f q ≫
        ιTerm (coneDiagram φ) p q n h (σ.comp (SimplexCategory.δ a).toOrderHom) ≫
          coneTotalXHom φ n) = _
  rw [inr_ιTerm_coneTotalXHom]

/-- The explicit signed total-cone comparison commutes with differentials.

Source: the cone-block comparison paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-total-cone-differential).

Proof: Test the equality on a diagonal generator labelled by a monotone string,
and then on each of its two cone summands. Put e_p=(-1)^p. The horizontal term
on a source generator is multiplied by e_(p-1) on the left and by -e_p on the
right; these are equal. The vertical source terms have coefficient -e_p^2=-1
on both sides. The off-diagonal term has coefficient e_p on both sides, by
naturality of the transformation. On a target generator the horizontal terms
are unchanged and the vertical terms have coefficient e_p. Use the cone
inclusion-differential identities, the two total-differential identities, and
the alternating face-map formula. In horizontal degree zero the horizontal
differential is zero on both sides. The identities e_p^2=1 and e_(p+1)=-e_p
finish the calculation. Every generator has finitely many face terms, so no
support or boundedness hypothesis is needed. -/
theorem coneTotalXHom_comm (n : ℤ) :
    coneTotalXHom φ n ≫ (CochainComplex.mappingCone (totalArrow φ)).d n (n + 1) =
      (total (coneDiagram φ)).d n (n + 1) ≫ coneTotalXHom φ (n + 1) := by
  apply ιTerm_hom_ext (coneDiagram φ) n
  intro p q h σ
  apply CochainComplex.mappingCone.ext_from (φ.app (σ 0)) (q + 1) q rfl
  · cases p with
    | zero =>
      have hq : q = n := by simpa using h
      subst q
      simp only [Category.assoc, inl_ιTerm_coneTotalXHom_assoc,
        pow_zero, one_smul]
      rw [CochainComplex.mappingCone.inl_v_d _ (n + 1) n (n + 1 + 1) (by omega) (by omega)]
      simp only [Preadditive.comp_sub, ιTerm_totalArrow_assoc, ιTerm_d_zero_assoc]
      change _ = (CochainComplex.mappingCone.inl (φ.app (σ 0))).v (n + 1) n (by omega) ≫
        (CochainComplex.mappingCone (φ.app (σ 0))).d n (n + 1) ≫ _
      rw [CochainComplex.mappingCone.inl_v_d_assoc _ (n + 1) n (n + 1 + 1)
        (by omega) (by omega)]
      simp only [Preadditive.sub_comp, Category.assoc,
        inr_ιTerm_coneTotalXHom, inl_ιTerm_coneTotalXHom, pow_zero, one_smul]
    | succ p =>
      simp only [Category.assoc, inl_ιTerm_coneTotalXHom_assoc,
        Preadditive.zsmul_comp]
      rw [CochainComplex.mappingCone.inl_v_d _ (n + 1) n (n + 1 + 1) (by omega) (by omega)]
      simp only [Preadditive.comp_sub, Category.assoc, ιTerm_totalArrow_assoc,
        ιTerm_d_succ_assoc, Preadditive.comp_add, Preadditive.comp_sum,
        Preadditive.comp_zsmul, Preadditive.sum_comp, Preadditive.zsmul_comp,
        Preadditive.add_comp, inl_face_XHom]
      change _ = _ + ((-1 : ℤ) ^ (p + 1)) •
        ((CochainComplex.mappingCone.inl (φ.app (σ 0))).v (q + 1) q (by omega) ≫
          (CochainComplex.mappingCone (φ.app (σ 0))).d q (q + 1) ≫
            ιTerm (coneDiagram φ) (p + 1) (q + 1) (n + 1) (by omega) σ ≫
              coneTotalXHom φ (n + 1))
      rw [CochainComplex.mappingCone.inl_v_d_assoc _ (q + 1) q (q + 1 + 1)
        (by omega) (by omega)]
      simp only [Preadditive.sub_comp, Category.assoc, smul_sub,
        inr_ιTerm_coneTotalXHom, inl_ιTerm_coneTotalXHom,
        Preadditive.comp_zsmul, smul_smul]
      simp only [smul_add, Finset.smul_sum, smul_smul, sign_square, one_smul]
      simp only [pow_succ, mul_neg, neg_mul, neg_smul,
        Finset.sum_neg_distrib, mul_comm, one_mul]
      abel
  · cases p with
    | zero =>
      have hq : q = n := by simpa using h
      subst q
      simp only [inr_ιTerm_coneTotalXHom_assoc]
      rw [CochainComplex.mappingCone.inr_f_d]
      simp only [ιTerm_d_zero_assoc]
      change _ = (CochainComplex.mappingCone.inr (φ.app (σ 0))).f n ≫
        (CochainComplex.mappingCone (φ.app (σ 0))).d n (n + 1) ≫ _
      rw [CochainComplex.mappingCone.inr_f_d_assoc]
      simp only [inr_ιTerm_coneTotalXHom]
    | succ p =>
      simp only [inr_ιTerm_coneTotalXHom_assoc]
      rw [CochainComplex.mappingCone.inr_f_d]
      simp only [ιTerm_d_succ_assoc, Preadditive.comp_add,
        Preadditive.comp_sum, Preadditive.comp_zsmul, Preadditive.sum_comp,
        Preadditive.zsmul_comp, Preadditive.add_comp,
        Category.assoc, inr_face_XHom]
      change _ = _ + ((-1 : ℤ) ^ (p + 1)) •
        ((CochainComplex.mappingCone.inr (φ.app (σ 0))).f q ≫
          (CochainComplex.mappingCone (φ.app (σ 0))).d q (q + 1) ≫
            ιTerm (coneDiagram φ) (p + 1) (q + 1) (n + 1) (by omega) σ ≫
              coneTotalXHom φ (n + 1))
      rw [CochainComplex.mappingCone.inr_f_d_assoc]
      simp only [inr_ιTerm_coneTotalXHom]

end CategoryTheory.PreorderBar
