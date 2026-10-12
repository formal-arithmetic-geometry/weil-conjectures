module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# The coefficient relation before passing to the quotient

Source: Stacks Project, More on Algebra, Tag 0EM0, proof of `lemma-helper-finite`.
-/

@[expose] public section

universe u v w z

open scoped BigOperators

namespace Algebra

/-- The upstairs relation with coefficients in the extended ideal, before taking a quotient.
Source: Stacks Project, More on Algebra, Tag 0EM0, proof of `lemma-helper-finite`.
(blueprint: lem-weil-pbc-gabber-upstairs-tensor-coefficients)

Proof: Lift the idempotent (1,0) over an etale neighbourhood preserving A/I (07M4).
Split the finite base change of B into its two idempotent factors. The first factor's
structure map has finite cokernel which is equal to I times itself; Nakayama (00DV)
gives g congruent to 1 modulo I annihilating this cokernel. Localize at g. The first
factor is now a quotient of the base C, and the image of b-1 lifts to a coefficient
in IC. In the second factor b lies in the extended ideal. The integral extended-ideal
annihilator (00H5) gives a monic polynomial congruent to X^e annihilating b there.
Multiply it by X, so its degree d is positive even if the second factor is zero.
Multiplying this polynomial by X-1-a, with a the first-factor lift of b-1, annihilates
both factors. Its difference from (X-1)X^d has degree at most d and coefficients in IC.
Each coefficient in IC is a finite sum of products c*i with c in C and i in I, hence
is represented by an element of C tensor_A I. Evaluation gives the displayed sum,
with signs absorbed into the coefficient tensors. C is flat (etale then localization)
and C/IC is A/I. Every maximal ideal of A contains I and has nonzero fibre in C;
the flat maximal-fibre criterion (00HP) therefore makes C faithfully flat. -/
theorem exists_gabber_upstairs_tensor_relation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (B₁ : Type w) (B₂ : Type z) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* (B₁ × B₂))
    (he : ∀ a : A, e (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a)) =
      (algebraMap (A ⧸ I) B₁ (Ideal.Quotient.mk I a),
        algebraMap (A ⧸ I) B₂ (Ideal.Quotient.mk I a)))
    (h₁ : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B) (hb : e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = (1, 0)) :
    ∃ (C : CommRingCat.{u}) (f : A →+* C),
      letI : Algebra A C := f.toAlgebra
      Module.FaithfullyFlat A C ∧ ∃ d : ℕ, 1 ≤ d ∧
        ∃ c : Fin (d + 1) → TensorProduct A C I,
          TensorProduct.tmul A (1 : C) ((b - 1) * b ^ d) =
            ∑ j : Fin (d + 1),
              (I.subtype.smulRight (b ^ (j : ℕ))).lTensor C (c j) := by
  sorry

end Algebra
