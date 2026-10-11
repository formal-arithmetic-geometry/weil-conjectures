/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# A lift of the fibre idempotent gives the localization isomorphism

Source: literature/stacks-project/more-algebra.tex:2542-2549, proof of Lemma Tag 09XH
(blueprint: lem-weil-pbc-integral-closure-finite-fibre-choose-g)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w₁ w₂ w₃ w₄

namespace AlgebraicGeometry

/-- A neighbourhood of the first factor of a finite fibre contains a principal open
on which the integral-closure map is an isomorphism.

Source: literature/stacks-project/more-algebra.tex:2542-2549, proof of Lemma Tag 09XH
(blueprint: lem-weil-pbc-integral-closure-finite-fibre-choose-g).
Here `B'` is `integralClosure A B`. Proof (the five steps of the node):
1. Lift the idempotent to `g₀`. The first factor has spectrum `V(K)`, where
   `K = IB' + (1 - g₀)B'`, by the quotient-prime correspondence
   (`def-weil-affine-spectrum`).
2. Write the complement of `U` as `V(J)`. Since `V(J)` and `V(K)` are disjoint,
   `J + K = B'` by `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`.
   Choose `1 = j + k`, with `j ∈ J` and `k ∈ K`.
3. Set `g = g₀ * j`. The relation `g₀ * (1 - g₀) ∈ IB'` gives `g - g₀ ∈ IB'`,
   while `g ∈ J` gives `D(g) ⊆ U`.
4. The inverse image of `D(g)` is `D(ι(g))`, by
   `lem-weil-pbc-morphism-into-affine-scheme`. Sections on these basic opens are
   `B'_g` and `B_g`, by `lem-weil-pbc-affine-ideals-closed-subscheme` (0) and
   `def-weil-ring-localization-away`.
5. Restrict the assumed isomorphism to `D(g)` and take sections. Its ring map
   commutes with restriction of global sections, hence is the induced localization
   map by uniqueness in `def-weil-ring-localization-away`; therefore it is bijective.
-/
theorem integralClosure_finite_fibre_choose_g
    (A : Type v) (B : Type u)
    (C₁ : Type w₁) (C₂ : Type w₂) (C₁' : Type w₃) (C₂' : Type w₄)
    [CommRing A] [CommRing B]
    [CommRing C₁] [CommRing C₂] [CommRing C₁'] [CommRing C₂']
    [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A)
    [Algebra (A ⧸ I) C₁] [Algebra (A ⧸ I) C₂]
    [Algebra (A ⧸ I) C₁'] [Algebra (A ⧸ I) C₂']
    [Module.Finite (A ⧸ I) C₁]
    (eB : (B ⧸ Ideal.map (algebraMap A B) I) ≃+* C₁ × C₂)
    (eB' : (integralClosure A B ⧸ Ideal.map (algebraMap A (integralClosure A B)) I) ≃+*
      C₁' × C₂')
    (heB : ∀ a : A,
      eB (Ideal.Quotient.mk _ (algebraMap A B a)) =
        algebraMap (A ⧸ I) (C₁ × C₂) (Ideal.Quotient.mk I a))
    (heB' : ∀ a : A,
      eB' (Ideal.Quotient.mk _ (algebraMap A (integralClosure A B) a)) =
        algebraMap (A ⧸ I) (C₁' × C₂') (Ideal.Quotient.mk I a))
    (f₁ : C₁' →ₐ[A ⧸ I] C₁) (f₂ : C₂' →ₐ[A ⧸ I] C₂)
    (hprod : ∀ b : integralClosure A B,
      eB (Ideal.Quotient.mk _ (algebraMap (integralClosure A B) B b)) =
        (f₁ (eB' (Ideal.Quotient.mk _ b)).1, f₂ (eB' (Ideal.Quotient.mk _ b)).2))
    (U : (Spec (.of (integralClosure A B))).Opens)
    (hU : ∀ p : PrimeSpectrum C₁',
      (PrimeSpectrum.comap (Ideal.Quotient.mk _)
        (PrimeSpectrum.comap ((RingHom.fst C₁' C₂').comp eB'.toRingHom) p) :
        PrimeSpectrum (integralClosure A B)) ∈ U)
    (hIso : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap (integralClosure A B) B)) ∣_ U)) :
    ∃ g : integralClosure A B,
      Ideal.Quotient.mk (Ideal.map (algebraMap A (integralClosure A B)) I) g =
        eB'.symm (1, 0) ∧
      (∀ p : PrimeSpectrum (integralClosure A B), g ∉ (p.1 : Set (integralClosure A B)) →
        (p : Spec (.of (integralClosure A B))) ∈ U) ∧
      Function.Bijective (Localization.awayMap (algebraMap (integralClosure A B) B) g) := by
  sorry

end AlgebraicGeometry
