/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.AlgebraicGeometry.PreorderBarTotal

/-! # The differential on a labelled total-bar generator

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace CategoryTheory.PreorderBar
variable {I : Type u} [Preorder I] {A : Type w} [Category.{v} A] [Preadditive A]
  [HasCoproducts.{u} A] [HasCoproducts.{0} A]
  (D : I ⥤ CochainComplex A ℤ)

def faceArrow {p : ℕ} (σ : Fin (p + 2) →o I) (a : Fin (p + 2)) :
    σ 0 ⟶ σ ((SimplexCategory.δ a).toOrderHom 0) :=
  homOfLE (σ.monotone (Fin.zero_le ((SimplexCategory.δ a).toOrderHom 0)))

lemma ιTerm_eq (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n)
    (σ : Fin (p + 1) →o I) :
    ιTerm D p q n h σ =
      (Sigma.ι (fun τ : Fin (p + 1) →o I ↦ D.obj (τ 0)) σ).f q ≫
        (bicomplex D).ιTotal (ComplexShape.up ℤ) p q n h := by
  let F := HomologicalComplex.eval A (ComplexShape.up ℤ) q
  change Sigma.ι (fun τ : Fin (p + 1) →o I ↦ F.obj (D.obj (τ 0))) σ ≫
    sigmaComparison F (fun τ : Fin (p + 1) →o I ↦ D.obj (τ 0)) ≫ _ = _
  rw [ι_comp_sigmaComparison_assoc]
  rfl

@[reassoc]
lemma ιTerm_D₂ (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n)
    (σ : Fin (p + 1) →o I) :
    ιTerm D p q n h σ ≫ (bicomplex D).D₂ (ComplexShape.up ℤ) n (n + 1) =
      ((-1 : ℤ) ^ p) • ((D.obj (σ 0)).d q (q + 1) ≫
        ιTerm D p (q + 1) (n + 1) (by omega) σ) := by
  rw [ιTerm_eq, Category.assoc, HomologicalComplex₂.ι_D₂]
  rw [(bicomplex D).d₂_eq (ComplexShape.up ℤ) p
    (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) (n + 1)
    (by change q + 1 - (p : ℤ) = n + 1; omega)]
  have he : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = (-1 : ℤˣ) ^ p := rfl
  rw [he, Linear.comp_units_smul]
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have hh := (Sigma.ι (fun τ : Fin (p + 1) →o I ↦ D.obj (τ 0)) σ).comm_assoc
    q (q + 1) ((bicomplex D).ιTotal (ComplexShape.up ℤ) p (q + 1) (n + 1) (by
      change q + 1 - (p : ℤ) = n + 1; omega))
  rw [ιTerm_eq]
  exact congrArg (fun z ↦ ((-1 : ℤ) ^ p) • z) hh

@[reassoc]
lemma ιTerm_D₁_zero (q n : ℤ) (h : q - (0 : ℕ) = n) (σ : Fin 1 →o I) :
    ιTerm D 0 q n h σ ≫ (bicomplex D).D₁ (ComplexShape.up ℤ) n (n + 1) = 0 := by
  rw [ιTerm_eq, Category.assoc, HomologicalComplex₂.ι_D₁]
  rw [(bicomplex D).d₁_eq_zero (ComplexShape.up ℤ) 0 q (n + 1) (by simp), comp_zero]

@[reassoc]
lemma ιTerm_D₁_succ (p : ℕ) (q n : ℤ) (h : q - ((p + 1 : ℕ) : ℤ) = n)
    (σ : Fin (p + 1 + 1) →o I) :
    ιTerm D (p + 1) q n h σ ≫ (bicomplex D).D₁ (ComplexShape.up ℤ) n (n + 1) =
      ∑ a : Fin (p + 2), ((-1 : ℤ) ^ a.val) •
        ((D.map (faceArrow σ a)).f q ≫
          ιTerm D p q (n + 1) (by omega) (σ.comp (SimplexCategory.δ a).toOrderHom)) := by
  rw [ιTerm_eq, Category.assoc, HomologicalComplex₂.ι_D₁]
  rw [(bicomplex D).d₁_eq (ComplexShape.up ℤ)
    (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl) q (n + 1)
    (by change q - (p : ℤ) = n + 1; omega)]
  change _ ≫ ((1 : ℤˣ) • _) = _
  rw [one_smul, ← Category.assoc, ← HomologicalComplex.comp_f]
  simp only [bicomplex, AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  change ((Sigma.ι (fun τ : Fin (p + 1 + 1) →o I ↦ D.obj (τ 0)) σ) ≫
    ∑ a : Fin (p + 2), ((-1 : ℤ) ^ a.val) •
      map D (SimplexCategory.δ a)).f q ≫ _ = _
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, ι_map,
    ιTerm_eq]
  change (HomologicalComplex.eval A (ComplexShape.up ℤ) q).map (∑ a : Fin (p + 2),
    ((-1 : ℤ) ^ a.val) •
      (D.map (faceArrow σ a) ≫
        Sigma.ι (fun τ : Fin (p + 1) →o I ↦ D.obj (τ 0))
          (σ.comp (SimplexCategory.δ a).toOrderHom))) ≫
    _ = _
  rw [Functor.map_sum]
  simp only [HomologicalComplex.eval_map, HomologicalComplex.zsmul_f_apply,
    HomologicalComplex.comp_f, Preadditive.sum_comp, Preadditive.zsmul_comp,
    Category.assoc]
  rfl

@[reassoc]
lemma ιTerm_d_zero (q n : ℤ) (h : q - (0 : ℕ) = n) (σ : Fin 1 →o I) :
    ιTerm D 0 q n h σ ≫ (total D).d n (n + 1) =
      (D.obj (σ 0)).d q (q + 1) ≫ ιTerm D 0 (q + 1) (n + 1) (by omega) σ := by
  simp only [total, HomologicalComplex₂.total_d, Preadditive.comp_add,
    ιTerm_D₁_zero, ιTerm_D₂, pow_zero, one_smul, zero_add]

/-- The differential on a labelled total-bar generator.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-total-differential).

Proof: Express the total generator as evaluation of a coproduct inclusion followed by its diagonal
inclusion. The first total differential is the horizontal alternating face-map differential, hence
the finite sum of the diagram face maps with coefficients (-1)^a. The second is the internal
differential times the prescribed total sign; commute it past the coproduct inclusion using its
cochain-map equation. At horizontal degree zero the first differential is zero. The total
differential is the sum of these two terms. -/
@[reassoc]
lemma ιTerm_d_succ (p : ℕ) (q n : ℤ) (h : q - ((p + 1 : ℕ) : ℤ) = n)
    (σ : Fin (p + 1 + 1) →o I) :
    ιTerm D (p + 1) q n h σ ≫ (total D).d n (n + 1) =
      (∑ a : Fin (p + 2), ((-1 : ℤ) ^ a.val) •
        ((D.map (faceArrow σ a)).f q ≫
          ιTerm D p q (n + 1) (by omega) (σ.comp (SimplexCategory.δ a).toOrderHom))) +
      ((-1 : ℤ) ^ (p + 1)) • ((D.obj (σ 0)).d q (q + 1) ≫
        ιTerm D (p + 1) (q + 1) (n + 1) (by omega) σ) := by
  simp only [total, HomologicalComplex₂.total_d, Preadditive.comp_add,
    ιTerm_D₁_succ, ιTerm_D₂]

end CategoryTheory.PreorderBar
