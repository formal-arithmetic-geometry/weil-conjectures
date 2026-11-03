/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ParameterRoot.ParameterRootAlgebra
public import WeilConjectures.AlgebraicGeometry.StrictLocalKummerTameModule
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Order.ULift

/-! # The explicit compatible-root quotient is a colimit

Source: ILO IX 2.1 and Stacks 04AX, polynomial quotient universal properties.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
namespace Algebra.ParameterRoot
open AlgebraicGeometry.ProEtale
variable {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) (p : ℕ)

abbrev fullRoot (n : TameRootOrder p) (i : Fin r) : tameRootAlgebra p t :=
  Ideal.Quotient.mk _ (MvPolynomial.X (i, n))

@[simp] theorem fullRoot_pow (n : TameRootOrder p) (i : Fin r) :
    fullRoot t p n i ^ n.val = algebraMap R (tameRootAlgebra p t) (t i) := by
  have hmem : MvPolynomial.X (i, n) ^ n.val - MvPolynomial.C (t i) ∈
      Ideal.span (tameRootRelations p t) := Ideal.subset_span (Or.inl ⟨i, n, rfl⟩)
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  change Ideal.Quotient.mk _ (MvPolynomial.X (i, n)) ^ n.val =
    Ideal.Quotient.mk _ (MvPolynomial.C (t i))
  simpa only [map_sub, map_pow, sub_eq_zero] using hz

/-- Include a finite level by its labelled root generators. -/
def inclusion (n : TameRootOrder p) : Ring t n.val →ₐ[R] tameRootAlgebra p t :=
  lift t n.val (fullRoot t p n) (fullRoot_pow t p n)

/-- A separate wrapper ensures that the order means divisibility, not numerical size. -/
structure DirectedIndex (p : ℕ) where
  order : TameRootOrder p

instance (p : ℕ) : Preorder (DirectedIndex p) where
  le i j := i.order.val ∣ j.order.val
  le_refl _ := dvd_refl _
  le_trans _ _ _ := dvd_trans

instance (p : ℕ) : Nonempty (DirectedIndex p) :=
  ⟨⟨⟨1, Nat.zero_lt_one, Nat.coprime_one_left p⟩⟩⟩

instance (p : ℕ) : IsDirectedOrder (DirectedIndex p) where
  directed i j := ⟨⟨⟨i.order.val * j.order.val,
    Nat.mul_pos i.order.property.1 j.order.property.1,
    Nat.coprime_mul_iff_left.mpr ⟨i.order.property.2, j.order.property.2⟩⟩⟩,
    dvd_mul_right _ _, dvd_mul_left _ _⟩

instance (p : ℕ) : IsDirectedOrder (ULift.{u} (DirectedIndex p)) where
  directed i j := by
    obtain ⟨k, hi, hj⟩ := exists_ge_ge i.down j.down
    exact ⟨⟨k⟩, hi, hj⟩

end Algebra.ParameterRoot
