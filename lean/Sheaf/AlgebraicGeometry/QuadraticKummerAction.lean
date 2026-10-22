/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.Algebra.CharP.Algebra

/-!
# A transposition in the quadratic Kummer fibre

Source: blueprint `lem-trf-devissage-generation`, proof Step 3.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open Polynomial

namespace AlgebraicGeometry

private theorem kummer_coordinate_not_square (k : Type u) [Field k]
    (r : RatFunc k) : r ^ 2 ≠ RatFunc.X := by
  intro h
  have hr : r ≠ 0 := by
    intro hr
    exact RatFunc.X_ne_zero (by simpa [hr] using h.symm)
  have hd := congrArg RatFunc.intDegree h
  rw [pow_two, RatFunc.intDegree_mul hr hr, RatFunc.intDegree_X] at hd
  omega

set_option backward.isDefEq.respectTransparency false in
/-- A geometric generic fibre of the quadratic Kummer cover has a transposition.
Source: blueprint `lem-trf-devissage-generation`, proof Step 3
(blueprint: lem-trf-quadratic-kummer-action).

Proof: the degree of a nonzero rational function is additive under multiplication,
whereas the coordinate has degree one. It therefore has no square root in k(t).
The polynomial z^2-t is irreducible by the prime-degree Kummer criterion. It has a
root r in an algebraic closure; its minimal polynomial is z^2-t. The other root -r
is distinct, since t is nonzero and the characteristic is five. Normality extends
the isomorphism between the two simple extensions to an automorphism of the
algebraic closure. This automorphism sends r to -r and fixes k(t). -/
theorem quadratic_kummer_generic_action (k : Type u) [Field k] [CharP k 5] :
    ∃ (r : AlgebraicClosure (RatFunc k))
      (σ : AlgebraicClosure (RatFunc k) ≃ₐ[RatFunc k] AlgebraicClosure (RatFunc k)),
      r ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) RatFunc.X ∧
      σ r = -r ∧ r ≠ -r := by
  let K := RatFunc k
  let Ω := AlgebraicClosure K
  let p : Polynomial K := Polynomial.X ^ 2 - Polynomial.C (RatFunc.X : K)
  have hp : Irreducible p := X_pow_sub_C_irreducible_of_prime (by decide)
    (kummer_coordinate_not_square k)
  have hm : p.Monic := monic_X_pow_sub_C _ (by decide)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero Ω p
    (ne_of_gt (degree_pos_of_irreducible hp))
  have he : r ^ 2 = algebraMap K Ω RatFunc.X := by
    change Polynomial.eval₂ (algebraMap K Ω) r p = 0 at hr
    dsimp only [p] at hr
    rw [eval₂_sub, eval₂_pow, eval₂_X, Polynomial.eval₂_C] at hr
    exact sub_eq_zero.mp hr
  have hmin : minpoly K r = p := (minpoly.eq_of_irreducible_of_monic hp hr hm).symm
  have hneg : aeval (-r) (minpoly K r) = 0 := by
    rw [hmin]
    change Polynomial.eval₂ (algebraMap K Ω) (-r) p = 0
    dsimp only [p]
    rw [eval₂_sub, eval₂_pow, eval₂_X, Polynomial.eval₂_C, neg_sq, he, sub_self]
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
    (Algebra.IsAlgebraic.isAlgebraic r) hneg
  refine ⟨r, σ, he, hσ, ?_⟩
  have hr0 : r ≠ 0 := by
    intro h
    have hX : algebraMap K Ω RatFunc.X = 0 := by simpa [h] using he.symm
    exact RatFunc.X_ne_zero ((algebraMap K Ω).injective (by simpa using hX))
  have htwo : (2 : Ω) ≠ 0 := by
    exact (CharP.cast_eq_zero_iff Ω 5 2).not.mpr (by decide)
  intro h
  have : (2 : Ω) * r = 0 := by simpa [two_mul] using eq_neg_iff_add_eq_zero.mp h
  exact (mul_ne_zero htwo hr0) this

end AlgebraicGeometry
