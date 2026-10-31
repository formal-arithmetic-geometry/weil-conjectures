/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-! # The formal exponential turns sums into products

Source: Milne, Lectures on Étale Cohomology, §26 p. 151 and proof of Theorem 27.6,
p. 156; Deligne, Weil I, §1.5 p. 276 (blueprint: lem-weil-power-series-exp-hom).

The formal exponential is Mathlib's exponential series with the argument substituted
for its variable. Integer powers are taken in the group of units of the series ring.
-/

@[expose] public section

universe u v

namespace PowerSeries

/-- The formal exponential preserves zero and addition, has the indicated inverse,
and converts finite integer linear combinations into products of integer powers.

Source: Milne, Lectures on Étale Cohomology, §26 p. 151 and proof of Theorem 27.6,
p. 156 (the step "move the inner sum outside"); Deligne, Weil I, §1.5 p. 276
(blueprint: lem-weil-power-series-exp-hom).

Proof:
1. Write E(U) for the exponential with U substituted (def-weil-power-series-exponential
   on def-weil-formal-power-series). Substitution at zero gives E(0)=1, and for U with
   zero constant coefficient E(U) has constant coefficient 1 (substitute U into exp - 1).
   The chain rule and exp' = exp give E(U)' = E(U) U'.
2. For fixed a, two series f, g with f' = f a, g' = g a and equal constant coefficients
   are equal: by strong induction on n, the degree-n coefficients of f a and g a involve
   only coefficients of degree at most n, so (n+1) coeff_{n+1} f = (n+1) coeff_{n+1} g,
   and n+1 cancels since the Q-module R is additively torsion-free.
3. Apply 2 to f = E(U+W), g = E(U)E(W), a = (U+W)': the chain and product rules give
   both equations and both constant coefficients are 1. Hence E(U+W) = E(U)E(W).
4. E(U)E(-U) = E(0) = 1 = E(-U)E(U), so E(U) is a unit with inverse E(-U), built
   explicitly.
5. On the kernel K of the constant coefficient, U ↦ E(U) is an additive homomorphism to
   the additive type tag of the unit group by 3 and E(0)=1. It preserves finite sums and
   integer multiples; removing the tag gives the finite product of integer powers.
-/
theorem exp_subst_hom (R : Type u) [CommRing R] [Algebra ℚ R] :
    (exp R).subst (0 : PowerSeries R) = 1 ∧
    (∀ (U W : PowerSeries R), constantCoeff U = 0 → constantCoeff W = 0 →
      (exp R).subst (U + W) = (exp R).subst U * (exp R).subst W) ∧
    (∀ (U : PowerSeries R), constantCoeff U = 0 →
      ∃ e : (PowerSeries R)ˣ, (e : PowerSeries R) = (exp R).subst U ∧
        (exp R).subst (-U) = ((e⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)) ∧
    (∀ (I : Type v) [Fintype I] (U : I → PowerSeries R) (ε : I → ℤ),
      (∀ i : I, constantCoeff (U i) = 0) →
      ∃ e : I → (PowerSeries R)ˣ,
        (∀ i : I, (e i : PowerSeries R) = (exp R).subst (U i)) ∧
        (exp R).subst (∑ i : I, ε i • U i) =
          ((∏ i : I, e i ^ ε i : (PowerSeries R)ˣ) : PowerSeries R)) := by
  classical
  have : IsAddTorsionFree R := .of_module_rat R
  let E : PowerSeries R → PowerSeries R := fun U ↦ (exp R).subst U
  have hzero : E 0 = 1 := by
    simp [E, subst_zero_eq_C_constantCoeff]
  have hconst (U : PowerSeries R) (hU : constantCoeff U = 0) :
      constantCoeff (E U) = 1 := by
    have h := constantCoeff_subst_eq_zero hU (exp R - 1) (by simp)
    rw [subst_sub (.of_constantCoeff_zero' hU)] at h
    have h' : constantCoeff (E U) - 1 = 0 := by
      rw [constantCoeff_eq]
      simpa [E, ← coe_substAlgHom (.of_constantCoeff_zero' hU)] using h
    exact sub_eq_zero.mp h'
  have hderiv (U : PowerSeries R) (hU : constantCoeff U = 0) :
      derivative R (E U) = E U * derivative R U := by
    dsimp only [E]
    rw [derivative_subst (.of_constantCoeff_zero' hU), derivative_exp]
  -- The differential equation determines successive coefficients uniquely.
  have hunique (f g a : PowerSeries R)
      (hf : derivative R f = f * a) (hg : derivative R g = g * a)
      (hc : constantCoeff f = constantCoeff g) : f = g := by
    ext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa only [coeff_zero_eq_constantCoeff] using hc
      | succ n =>
        have hm : coeff n (f * a) = coeff n (g * a) := by
          simp only [coeff_mul]
          apply Finset.sum_congr rfl
          rintro ⟨i, j⟩ hij
          rw [ih i (by have := Finset.mem_antidiagonal.mp hij; omega)]
        rw [← hf, ← hg, coeff_derivative, coeff_derivative] at hm
        have hm' : (n + 1) • coeff (n + 1) f = (n + 1) • coeff (n + 1) g := by
          simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm] using hm
        exact (smul_right_inj (Nat.succ_ne_zero n)).mp hm'
  have hadd (U W : PowerSeries R) (hU : constantCoeff U = 0)
      (hW : constantCoeff W = 0) : E (U + W) = E U * E W := by
    apply hunique _ _ (derivative R (U + W))
    · exact hderiv _ (by simp [hU, hW])
    · rw [Derivation.leibniz, hderiv _ hU, hderiv _ hW, map_add]
      simp only [smul_eq_mul]
      ring
    · rw [hconst (U + W) (by simp [hU, hW]), map_mul, hconst U hU, hconst W hW,
        one_mul]
  let e (U : PowerSeries R) (hU : constantCoeff U = 0) : (PowerSeries R)ˣ :=
    { val := E U
      inv := E (-U)
      val_inv := by rw [← hadd U (-U) hU (by simp [hU]), add_neg_cancel, hzero]
      inv_val := by rw [← hadd (-U) U (by simp [hU]) hU, neg_add_cancel, hzero] }
  refine ⟨hzero, hadd, ?_, ?_⟩
  · intro U hU
    exact ⟨e U hU, rfl, rfl⟩
  · intro I _ U ε hU
    let K := RingHom.ker (constantCoeff : PowerSeries R →+* R)
    let F : K →+ Additive (PowerSeries R)ˣ :=
      { toFun := fun x ↦ Additive.ofMul (e x x.property)
        map_zero' := by apply Units.ext; exact hzero
        map_add' := by intro x y; apply Units.ext; exact hadd x y x.property y.property }
    let V : I → K := fun i ↦ ⟨U i, hU i⟩
    refine ⟨fun i ↦ e (U i) (hU i), fun _ ↦ rfl, ?_⟩
    have hs : F (∑ i, ε i • V i) = ∑ i, ε i • F (V i) := by
      simp only [map_sum, map_zsmul]
    have ht := congrArg (fun x : Additive (PowerSeries R)ˣ ↦
      ((Additive.toMul x : (PowerSeries R)ˣ) : PowerSeries R)) hs
    change E ((∑ i, ε i • V i : K) : PowerSeries R) = _ at ht
    simpa [F, V, e, E] using ht

end PowerSeries
