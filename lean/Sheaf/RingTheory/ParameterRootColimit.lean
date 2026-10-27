/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.ParameterRootAlgebra
public import Sheaf.Paper.StrictLocalKummerTameModule
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

@[simp] theorem fullRoot_compat (n m : TameRootOrder p) (h : n.val ∣ m.val)
    (i : Fin r) : fullRoot t p m i ^ (m.val / n.val) = fullRoot t p n i := by
  have hmem : MvPolynomial.X (i, m) ^ (m.val / n.val) - MvPolynomial.X (i, n) ∈
      Ideal.span (tameRootRelations p t) := Ideal.subset_span (Or.inr ⟨i, n, m, h, rfl⟩)
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simpa only [map_sub, map_pow, sub_eq_zero] using hz

/-- Include a finite level by its labelled root generators. -/
def inclusion (n : TameRootOrder p) : Ring t n.val →ₐ[R] tameRootAlgebra p t :=
  lift t n.val (fullRoot t p n) (fullRoot_pow t p n)

@[simp] theorem inclusion_root (n : TameRootOrder p) (i : Fin r) :
    inclusion t p n (root t n.val i) = fullRoot t p n i := lift_root ..

theorem inclusion_comp (n m : TameRootOrder p) (h : n.val ∣ m.val) :
    (inclusion t p m).comp (transition t n.val m.val h) = inclusion t p n := by
  apply hom_ext
  intro i
  simp only [AlgHom.comp_apply, transition_root, map_pow, inclusion_root]
  exact fullRoot_compat t p n m h i

/-- The quotient is the ring colimit of the finite root levels. -/
theorem full_isColimit {S : Type v} [CommRing S]
    (a : ∀ n : TameRootOrder p, Ring t n.val →+* S)
    (ha : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (a m).comp (transition t n.val m.val h).toRingHom = a n) :
    ∃! g : tameRootAlgebra p t →+* S,
      ∀ n, g.comp (inclusion t p n).toRingHom = a n := by
  let one : TameRootOrder p := ⟨1, Nat.zero_lt_one, Nat.coprime_one_left p⟩
  let c : R →+* S := (a one).comp (algebraMap R _)
  have hc (n : TameRootOrder p) (b : R) : a n (algebraMap R _ b) = c b := by
    have he := RingHom.congr_fun (ha one n (one_dvd _)) (algebraMap R _ b)
    change a n (transition t one.val n.val _ (algebraMap R _ b)) = c b at he
    simpa only [AlgHom.commutes] using he
  let x : Fin r × TameRootOrder p → S := fun z ↦ a z.2 (root t z.2.val z.1)
  let ev := MvPolynomial.eval₂Hom c x
  have hk : Ideal.span (tameRootRelations p t) ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro z (⟨i, n, rfl⟩ | ⟨i, n, m, h, rfl⟩)
    · change ev (MvPolynomial.X (i, n) ^ n.val - MvPolynomial.C (t i)) = 0
      simp only [ev, map_sub, map_pow, MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_C]
      change (a n (root t n.val i)) ^ n.val - c (t i) = 0
      rw [← map_pow, root_pow, hc, sub_self]
    · change ev (MvPolynomial.X (i, m) ^ (m.val / n.val) - MvPolynomial.X (i, n)) = 0
      simp only [ev, map_sub, map_pow, MvPolynomial.eval₂Hom_X']
      change (a m (root t m.val i)) ^ (m.val / n.val) - a n (root t n.val i) = 0
      have he := RingHom.congr_fun (ha n m h) (root t n.val i)
      change a m (transition t n.val m.val h (root t n.val i)) = _ at he
      rw [transition_root, map_pow] at he
      exact sub_eq_zero.mpr he
  let g := Ideal.Quotient.lift _ ev (fun z hz ↦ hk hz)
  have hgroot (n : TameRootOrder p) (i : Fin r) :
      g (fullRoot t p n i) = a n (root t n.val i) := by
    simp [g, fullRoot, ev, x, Ideal.Quotient.lift_mk]
  have hgcoeff (b : R) : g (algebraMap R _ b) = c b := by
    change g (Ideal.Quotient.mk _ (MvPolynomial.C b)) = _
    simp [g, ev, Ideal.Quotient.lift_mk]
  have hg (n : TameRootOrder p) : g.comp (inclusion t p n).toRingHom = a n := by
    apply ringHom_ext
    · ext b
      change g (inclusion t p n (algebraMap R _ b)) = a n (algebraMap R _ b)
      rw [AlgHom.commutes, hgcoeff, hc]
    · intro i
      change g (inclusion t p n (root t n.val i)) = a n (root t n.val i)
      rw [inclusion_root, hgroot]
  refine ⟨g, hg, fun g' hg' ↦ ?_⟩
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro b
    have he := RingHom.congr_fun (hg' one) (algebraMap R _ b)
    change g' (algebraMap R _ b) = g (algebraMap R _ b)
    rw [hgcoeff]
    change g' (inclusion t p one (algebraMap R _ b)) = c b at he
    rwa [AlgHom.commutes] at he
  · rintro ⟨i, n⟩
    have he := RingHom.congr_fun (hg' n) (root t n.val i)
    change g' (fullRoot t p n i) = g (fullRoot t p n i)
    rw [hgroot]
    change g' (inclusion t p n (root t n.val i)) = _ at he
    rwa [inclusion_root] at he

/-- With no parameters the coefficient inclusion is bijective, even for the full quotient. -/
theorem full_empty_bijective (t : Fin 0 → R) :
    Function.Bijective (algebraMap R (tameRootAlgebra p t)) := by
  let a : ∀ n : TameRootOrder p, Ring t n.val →+* R :=
    fun n ↦ (emptyEquiv n.val t).toRingHom
  have ha : ∀ n m (h : n.val ∣ m.val),
      (a m).comp (transition t n.val m.val h).toRingHom = a n := by
    intro n m h
    apply ringHom_ext
    · ext b
      change emptyEquiv m.val t (transition t n.val m.val h (algebraMap R _ b)) =
        emptyEquiv n.val t (algebraMap R _ b)
      simp only [AlgHom.commutes, AlgEquiv.commutes]
    · intro i
      exact Fin.elim0 i
  obtain ⟨g, hg, hu⟩ := full_isColimit t p a ha
  let one : TameRootOrder p := ⟨1, Nat.zero_lt_one, Nat.coprime_one_left p⟩
  have hc (b : R) : g (algebraMap R _ b) = b := by
    have he := RingHom.congr_fun (hg one) (algebraMap R _ b)
    change g (inclusion t p one (algebraMap R _ b)) = emptyEquiv one.val t _ at he
    simpa only [AlgHom.commutes, AlgEquiv.commutes, Algebra.algebraMap_self,
      RingHom.id_apply] using he
  have hi : (algebraMap R (tameRootAlgebra p t)).comp g = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro b
      change algebraMap R _ (g (algebraMap R _ b)) = algebraMap R _ b
      rw [hc]
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
  exact ⟨Function.LeftInverse.injective hc, fun b ↦ ⟨g b, RingHom.congr_fun hi b⟩⟩

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
