/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Completion comparison from ideal-power quotient isomorphisms

Source: the inverse-limit calculation in lem-trf-smooth-rational-point-completion,
Steps 5 and 7. The quotient maps are the canonical maps induced by the ring homomorphism.
-/

@[expose] public section

set_option autoImplicit false

namespace AdicCompletion

private theorem completion_eval_factor {A : Type*} [CommRing A] (I : Ideal A)
    {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on I A with
  | h a =>
    simp only [AdicCompletion.evalₐ_mk]
    exact AdicCompletion.Ideal.mk_eq_mk I h a

/-- Bijective maps on all ideal-power quotients induce a completion equivalence,
with the induced map on every quotient coordinate.

Source: the inverse-limit argument in Steps 5 and 7 of
lem-trf-smooth-rational-point-completion, using the compatible-sequence definition.
(blueprint: lem-trf-completion-equiv-power-quotients)

Proof: Replace each bijective quotient map by its ring equivalence. The maps commute
with reduction, as checked on representatives; their inverses therefore commute too.
Lift the two compatible families to maps of completions. Evaluation at every level
shows that their composites are identities and gives the asserted coordinate formula.
This also covers exponent zero, the unit ideal, the zero ideal and zero rings. -/
theorem equiv_of_powerQuotient_bijective
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (J : Ideal B) (h : I ≤ J.comap f)
    (hbij : ∀ n : ℕ, Function.Bijective
      (Ideal.quotientMap (J ^ n) f
        ((pow_le_pow_left' h n).trans (Ideal.le_comap_pow f n)))) :
    ∃ E : AdicCompletion I A ≃+* AdicCompletion J B,
      ∀ n x, AdicCompletion.evalₐ J n (E x) =
        Ideal.quotientMap (J ^ n) f
          ((pow_le_pow_left' h n).trans (Ideal.le_comap_pow f n))
          (AdicCompletion.evalₐ I n x) := by
  let e (n : ℕ) := RingEquiv.ofBijective
    (Ideal.quotientMap (J ^ n) f
      ((pow_le_pow_left' h n).trans (Ideal.le_comap_pow f n))) (hbij n)
  have he {m n : ℕ} (hle : m ≤ n) (x : A ⧸ I ^ n) :
      Ideal.Quotient.factorPow J hle (e n x) =
        e m (Ideal.Quotient.factorPow I hle x) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have he' {m n : ℕ} (hle : m ≤ n) (x : B ⧸ J ^ n) :
      Ideal.Quotient.factorPow I hle ((e n).symm x) =
        (e m).symm (Ideal.Quotient.factorPow J hle x) := by
    apply (e m).injective
    rw [← he hle, (e n).apply_symm_apply, (e m).apply_symm_apply]
  let F := AdicCompletion.liftRingHom J
    (fun n => (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom)
    (fun hle => RingHom.ext fun x => by
      exact (he hle _).trans (congrArg (e _) (completion_eval_factor I hle x)))
  let G := AdicCompletion.liftRingHom I
    (fun n => (e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom)
    (fun hle => RingHom.ext fun x => by
      exact (he' hle _).trans (congrArg (e _).symm (completion_eval_factor J hle x)))
  have hFG : F.comp G = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ _ n (F (G x)) = _
    rw [AdicCompletion.evalₐ_liftRingHom, RingHom.comp_apply]
    change e n (AdicCompletion.evalₐ I n (G x)) = AdicCompletion.evalₐ J n x
    rw [AdicCompletion.evalₐ_liftRingHom]
    exact (e n).apply_symm_apply _
  have hGF : G.comp F = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ _ n (G (F x)) = _
    rw [AdicCompletion.evalₐ_liftRingHom, RingHom.comp_apply]
    change (e n).symm (AdicCompletion.evalₐ J n (F x)) = AdicCompletion.evalₐ I n x
    rw [AdicCompletion.evalₐ_liftRingHom]
    exact (e n).symm_apply_apply _
  refine ⟨RingEquiv.ofRingHom F G hFG hGF, ?_⟩
  intro n x
  change AdicCompletion.evalₐ J n (F x) = _
  exact AdicCompletion.evalₐ_liftRingHom _ _ _ n x

end AdicCompletion
