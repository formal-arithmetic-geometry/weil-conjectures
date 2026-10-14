/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.AlgebraicGeometry.PreorderBarTotal
public import Mathlib.Algebra.Homology.Homotopy

/-! # Horizontal homotopies on mixed bar totals

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.PreorderBar
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.up ℤ)}
  [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
set_option backward.isDefEq.respectTransparency false in
/-- Horizontal homotopies on mixed bar totals.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-horizontal-homotopy).

Proof: On the summand of horizontal degree p and vertical degree q, use the horizontal homotopy
component
into horizontal degree p+1, followed by its diagonal inclusion. It lowers total degree q-p by one.
Its horizontal boundary is the supplied homotopy equation. Its two vertical terms cancel because
the total signs in adjacent columns are opposite. Coproduct extensionality proves the homotopy
equation, including the zero horizontal boundary at p=0. -/
noncomputable def horizontalHomotopy {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (HomologicalComplex₂.total.map f (ComplexShape.up ℤ))
      (HomologicalComplex₂.total.map g (ComplexShape.up ℤ)) := by
  classical
  let H : ∀ n m : ℤ, (K.total (ComplexShape.up ℤ)).X n ⟶
      (L.total (ComplexShape.up ℤ)).X m := fun n m ↦
    K.totalDesc (fun p q _ ↦ (h.hom p (p + 1)).f q ≫
      L.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) q m)
  have hH (p : ℕ) (q n m : ℤ) (hpq : q - (p : ℤ) = n) :
      K.ιTotal (ComplexShape.up ℤ) p q n hpq ≫ H n m =
        (h.hom p (p + 1)).f q ≫
          L.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) q m := by
    exact K.ι_totalDesc _ _ _ _
  refine { hom := H, zero := ?_, comm := ?_ }
  · intro n m hnm
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    rw [hH]
    have hz : ¬ q - ((p + 1 : ℕ) : ℤ) = m := by
      change ¬ m + 1 = n at hnm
      change q - (p : ℤ) = n at hpq
      omega
    rw [L.ιTotalOrZero_eq_zero _ _ _ _ hz, comp_zero]
    simp only [comp_zero]
  · intro n
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)]
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change q - (p : ℤ) = n at hpq
    subst n
    simp only [HomologicalComplex₂.ιTotal_map, Preadditive.comp_add]
    change _ =
      K.ιTotal (ComplexShape.up ℤ) p q (q - p) rfl ≫
          (K.total (ComplexShape.up ℤ)).d (q - p) (q - p + 1) ≫
            H (q - p + 1) (q - p) +
        K.ιTotal (ComplexShape.up ℤ) p q (q - p) rfl ≫
          H (q - p) (q - p - 1) ≫
            (L.total (ComplexShape.up ℤ)).d (q - p - 1) (q - p) +
        (g.f p).f q ≫ L.ιTotal (ComplexShape.up ℤ) p q (q - p) rfl
    simp only [← Category.assoc]
    rw [hH]
    rw [L.ιTotalOrZero_eq (ComplexShape.up ℤ) (p + 1) q (q - p - 1)
      (by change q - ((p + 1 : ℕ) : ℤ) = q - p - 1; omega)]
    simp only [Category.assoc, HomologicalComplex₂.total_d, Preadditive.comp_add,
      Preadditive.add_comp, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂]
    rw [L.d₁_eq' (ComplexShape.up ℤ)
        (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl),
      L.d₂_eq' (ComplexShape.up ℤ) (p + 1)
        (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl)]
    simp only [show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p + 1, q) = 1 from rfl, one_smul]
    rw [L.ιTotalOrZero_eq (ComplexShape.up ℤ) p q (q - p) rfl]
    rw [K.d₂_eq' (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl)]
    rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) p (q + 1) (q - p + 1)
      (by change q + 1 - (p : ℤ) = q - p + 1; omega)]
    simp only [Linear.units_smul_comp, Category.assoc, hH, Linear.comp_units_smul]
    rw [L.ιTotalOrZero_eq (ComplexShape.up ℤ) (p + 1) (q + 1) (q - p)
      (by change q + 1 - ((p + 1 : ℕ) : ℤ) = q - p; omega)]
    have he (a : ℕ) (b : ℤ) :
        ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (a, b) = (-1 : ℤˣ) ^ a := rfl
    simp only [he, pow_succ, Units.neg_smul, mul_neg, mul_one]
    rw [← (h.hom p (p + 1)).comm_assoc q (q + 1)]
    cases p with
    | zero =>
      rw [K.d₁_eq_zero (ComplexShape.up ℤ) 0 q _ (by simp), zero_comp]
      have hh := congrArg (fun z ↦ z.f q) (h.comm 0)
      simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        zero_add, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f] at hh
      rw [hh]
      simp only [Preadditive.add_comp, Category.assoc]
      abel
    | succ p =>
      rw [K.d₁_eq' (ComplexShape.up ℤ)
        (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl)]
      simp only [show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p + 1, q) = 1 from rfl, one_smul]
      rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) p q (q - (p + 1 : ℕ) + 1)
        (by change q - (p : ℤ) = q - ((p + 1 : ℕ) : ℤ) + 1; omega)]
      simp only [Category.assoc, hH]
      rw [L.ιTotalOrZero_eq (ComplexShape.up ℤ) (p + 1) q (q - (p + 1 : ℕ)) rfl]
      have hh := congrArg (fun z ↦ z.f q) (h.comm (p + 1))
      simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
        HomologicalComplex.add_f_apply, HomologicalComplex.comp_f] at hh
      rw [hh]
      simp only [Preadditive.add_comp, Category.assoc]
      abel
end CategoryTheory.PreorderBar
