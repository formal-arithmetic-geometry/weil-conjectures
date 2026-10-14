/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.AlgebraicGeometry.PreorderBarConeDiagram
import Sheaf.AlgebraicGeometry.PreorderBarTotalSplit

/-! # The explicit degreewise total-cone comparison

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.PreorderBar
variable {I : Type u} [Preorder I] {A : Type w} [Category.{v} A] [Preadditive A]
  [HasBinaryBiproducts A] [HasCoproducts.{u} A] [HasCoproducts.{0} A]
  {D E : I ⥤ CochainComplex A ℤ} (φ : D ⟶ E)

noncomputable def sameIndexMap : D ⟶ orderFunctor (OrderHom.id : I →o I) ⋙ E where
  app := φ.app
  naturality := φ.naturality

noncomputable def totalArrow : total D ⟶ total E :=
  totalMap D E OrderHom.id (sameIndexMap φ)

noncomputable def coneTotalXHom (n : ℤ) :
    (total (coneDiagram φ)).X n ⟶ (CochainComplex.mappingCone (totalArrow φ)).X n :=
  (bicomplex (coneDiagram φ)).totalDesc (fun p q h ↦
    (columnXIso (coneDiagram φ) p q).hom ≫ Sigma.desc (fun σ ↦
      (CochainComplex.mappingCone.fst (φ.app (σ 0))).1.v q (q + 1) rfl ≫
        (((-1 : ℤ) ^ p) • (ιTerm D p (q + 1) (n + 1) (by
          change q - (p : ℤ) = n at h; omega) σ ≫
          (CochainComplex.mappingCone.inl (totalArrow φ)).v (n + 1) n (by omega))) +
      (CochainComplex.mappingCone.snd (φ.app (σ 0))).v q q (add_zero q) ≫
        ιTerm E p q n h σ ≫ (CochainComplex.mappingCone.inr (totalArrow φ)).f n))

noncomputable def coneTotalXInv (n : ℤ) :
    (CochainComplex.mappingCone (totalArrow φ)).X n ⟶ (total (coneDiagram φ)).X n :=
  (CochainComplex.mappingCone.fst (totalArrow φ)).1.v n (n + 1) rfl ≫
    (bicomplex D).totalDesc (fun p q h ↦
      (columnXIso D p q).hom ≫ Sigma.desc (fun σ ↦
        ((-1 : ℤ) ^ p) •
          ((CochainComplex.mappingCone.inl (φ.app (σ 0))).v q (q - 1) (by omega) ≫
            ιTerm (coneDiagram φ) p (q - 1) n (by
              change q - (p : ℤ) = n + 1 at h; omega) σ))) +
  (CochainComplex.mappingCone.snd (totalArrow φ)).v n n (add_zero n) ≫
    (bicomplex E).totalDesc (fun p q h ↦
      (columnXIso E p q).hom ≫ Sigma.desc (fun σ ↦
        (CochainComplex.mappingCone.inr (φ.app (σ 0))).f q ≫
          ιTerm (coneDiagram φ) p q n h σ))

@[reassoc (attr := simp)]
lemma ιTerm_coneTotalXHom (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n)
    (σ : Fin (p + 1) →o I) :
    ιTerm (coneDiagram φ) p q n h σ ≫ coneTotalXHom φ n =
      (CochainComplex.mappingCone.fst (φ.app (σ 0))).1.v q (q + 1) rfl ≫
        (((-1 : ℤ) ^ p) • (ιTerm D p (q + 1) (n + 1) (by omega) σ ≫
          (CochainComplex.mappingCone.inl (totalArrow φ)).v (n + 1) n (by omega))) +
      (CochainComplex.mappingCone.snd (φ.app (σ 0))).v q q (add_zero q) ≫
        ιTerm E p q n h σ ≫ (CochainComplex.mappingCone.inr (totalArrow φ)).f n := by
  simp [ιTerm, coneTotalXHom, Category.assoc]

@[reassoc (attr := simp)]
lemma inl_ιTerm_coneTotalXHom (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n)
    (σ : Fin (p + 1) →o I) :
    (CochainComplex.mappingCone.inl (φ.app (σ 0))).v (q + 1) q (by omega) ≫
      ιTerm (coneDiagram φ) p q n h σ ≫ coneTotalXHom φ n =
    ((-1 : ℤ) ^ p) • (ιTerm D p (q + 1) (n + 1) (by omega) σ ≫
      (CochainComplex.mappingCone.inl (totalArrow φ)).v (n + 1) n (by omega)) := by
  simp only [ιTerm_coneTotalXHom, Preadditive.comp_add,
    Preadditive.comp_zsmul,
    CochainComplex.mappingCone.inl_v_fst_v_assoc,
    CochainComplex.mappingCone.inl_v_snd_v_assoc,
    zero_comp, add_zero]

@[reassoc (attr := simp)]
lemma inr_ιTerm_coneTotalXHom (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n)
    (σ : Fin (p + 1) →o I) :
    (CochainComplex.mappingCone.inr (φ.app (σ 0))).f q ≫
      ιTerm (coneDiagram φ) p q n h σ ≫ coneTotalXHom φ n =
    ιTerm E p q n h σ ≫ (CochainComplex.mappingCone.inr (totalArrow φ)).f n := by
  simp

@[reassoc (attr := simp)]
lemma inl_coneTotalXInv_ιTerm (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n + 1)
    (σ : Fin (p + 1) →o I) :
    ιTerm D p q (n + 1) h σ ≫
      (CochainComplex.mappingCone.inl (totalArrow φ)).v (n + 1) n (by omega) ≫
      coneTotalXInv φ n =
    ((-1 : ℤ) ^ p) •
      ((CochainComplex.mappingCone.inl (φ.app (σ 0))).v q (q - 1) (by omega) ≫
        ιTerm (coneDiagram φ) p (q - 1) n (by omega) σ) := by
  simp [coneTotalXInv, ιTerm, Category.assoc, Preadditive.comp_add,
    ]

@[reassoc (attr := simp)]
lemma inr_coneTotalXInv_ιTerm (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n)
    (σ : Fin (p + 1) →o I) :
    ιTerm E p q n h σ ≫ (CochainComplex.mappingCone.inr (totalArrow φ)).f n ≫
      coneTotalXInv φ n =
    (CochainComplex.mappingCone.inr (φ.app (σ 0))).f q ≫
      ιTerm (coneDiagram φ) p q n h σ := by
  simp [coneTotalXInv, ιTerm, Category.assoc, Preadditive.comp_add]

lemma sign_square (p : ℕ) : (-1 : ℤ) ^ p * (-1 : ℤ) ^ p = 1 := by
  rw [← mul_pow]
  simp

lemma coneTotalXHom_inv (n : ℤ) :
    coneTotalXHom φ n ≫ coneTotalXInv φ n = 𝟙 _ := by
  apply ιTerm_hom_ext (coneDiagram φ) n
  intro p q h σ
  apply CochainComplex.mappingCone.ext_from (φ.app (σ 0)) (q + 1) q rfl
  · simp only [Category.assoc, Category.comp_id, inl_ιTerm_coneTotalXHom_assoc,
      Preadditive.zsmul_comp, inl_coneTotalXInv_ιTerm, smul_smul, sign_square, one_smul]
    congr! 3 <;> omega
  · simp only [Category.comp_id, inr_ιTerm_coneTotalXHom_assoc,
      inr_coneTotalXInv_ιTerm]

lemma coneTotalXInv_hom (n : ℤ) :
    coneTotalXInv φ n ≫ coneTotalXHom φ n = 𝟙 _ := by
  apply CochainComplex.mappingCone.ext_from (totalArrow φ) (n + 1) n rfl
  · apply ιTerm_hom_ext D (n + 1)
    intro p q h σ
    obtain ⟨q, rfl⟩ : ∃ q' : ℤ, q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Category.assoc, inl_coneTotalXInv_ιTerm_assoc,
      Preadditive.zsmul_comp, Category.comp_id]
    have hh := inl_ιTerm_coneTotalXHom φ p q n (by omega) σ
    have hh' :
        (CochainComplex.mappingCone.inl (φ.app (σ 0))).v (q + 1) (q + 1 - 1)
            (by omega) ≫
          ιTerm (coneDiagram φ) p (q + 1 - 1) n (by omega) σ ≫ coneTotalXHom φ n =
        ((-1 : ℤ) ^ p) • (ιTerm D p (q + 1) (n + 1) h σ ≫
          (CochainComplex.mappingCone.inl (totalArrow φ)).v (n + 1) n (by omega)) := by
      convert! hh using 1
      congr! 3 <;> omega
    rw [hh']
    simp only [smul_smul, sign_square, one_smul]
  · apply ιTerm_hom_ext E n
    intro p q h σ
    simp only [inr_coneTotalXInv_ιTerm_assoc,
      inr_ιTerm_coneTotalXHom, Category.comp_id]

/-- The explicit degreewise total-cone comparison.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: def-sc-preorder-bar-total-cone).

Proof: On a cone summand in bar degree p and internal degree q, send its source summand to the
source of
the cone of totalArrow with coefficient (-1)^p, and send its target summand to the target with
coefficient 1. Use the corresponding diagonal inclusions. Define the inverse by totalDesc on
source and target with the same coefficients. The cone projections define these maps without
existence choices. Test composites on both cone inclusions and every bar generator. They reduce to
identity because ((-1)^p)^2=1. This constructs coneTotalXIso in each degree. -/
noncomputable def coneTotalXIso (n : ℤ) :
    (total (coneDiagram φ)).X n ≅ (CochainComplex.mappingCone (totalArrow φ)).X n where
  hom := coneTotalXHom φ n
  inv := coneTotalXInv φ n
  hom_inv_id := coneTotalXHom_inv φ n
  inv_hom_id := coneTotalXInv_hom φ n

end CategoryTheory.PreorderBar
