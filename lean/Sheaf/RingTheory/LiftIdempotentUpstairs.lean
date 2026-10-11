/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Lifting an idempotent upstairs after an étale neighbourhood

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 07M4
(blueprint: lem-weil-pbc-lift-idempotent-upstairs).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- An idempotent modulo an ideal lifts after an étale base change preserving the
quotient.  The equivalence `β` records the canonical tensor--quotient
identification induced by `α`; the final equality is precisely the lifting
condition under that identification.
Source: Stacks Project, More on Algebra, Lemma Tag 07M4
(blueprint: lem-weil-pbc-lift-idempotent-upstairs).

Proof plan (the eight steps of the node):
1. Choose a lift `y` of `ebar`. By
   `lem-weil-pbc-integral-idempotent-annihilating-polynomial`, choose a monic
   annihilator `f` reducing to `x^d (x - 1)^d`, with `d ≥ 1`.
2. The factors `x^d` and `(x - 1)^d` are coprime: expand
   `(x - (x - 1))^(2*d - 1)` and each summand is divisible by one factor.
   Apply `lem-weil-pbc-lift-coprime-factorization-etale` to obtain an étale
   neighbourhood `A₁` preserving `A/I` and a factorization `f = g*h`.
3. Put `B₁ = B ⊗[A] A₁`; it remains integral by
   `lem-weil-pbc-integral-base-change`. The canonical quotient isomorphism
   transports `ebar` to `ebar₁`. For `y₁ = y ⊗ 1`, put `b₁ = g(y₁)` and
   `b₂ = h(y₁)`. Their product is zero, and their reductions are `ebar₁`
   and `(-1)^d * (1 - ebar₁)`.
4. Thus `J = (b₁,b₂)` satisfies `J + I*B₁ = B₁`. By
   `lem-weil-pbc-integral-spec-closed-map`, the image of `V(J)` is closed
   and disjoint from `V(I*A₁)`. Apply
   `lem-weil-pbc-separate-image-closed-from-closed` to get `a = 1 mod I*A₁`
   whose image in `B₁` lies in `J`.
5. Localize `A₁` at `a`. By `lem-weil-pbc-principal-localization-open-immersion`
   and `lem-weil-pbc-etale-composition-cancellation`, `A₂` is étale over `A`.
   Since `a = 1 mod I*A₁`, this preserves the quotient. In `B₂ = B₁ ⊗[A₁] A₂`
   the images of `b₁,b₂` generate the unit ideal and still have product zero.
6. Therefore `Spec B₂ = D(b₁) ⨿ D(b₂)`. By
   `lem-weil-pbc-spec-clopen-idempotent`, let `e` be the idempotent with
   `D(e) = D(b₁)` (if `1 = u*b₁ + v*b₂`, take `e = u*b₁`).
7. In `B₂/I*B₂`, both the reduction of `e` and the transported `ebar` are
   idempotent with the same basic open. Uniqueness in
   `lem-weil-pbc-spec-clopen-idempotent` identifies them.
8. Take `A' = A₂` and transport `e` along tensor associativity to `e'`.
   The quotient equivalences are induced by the structure maps, as recorded
   by their values on representatives. Hence `β ebar` is the reduction of `e'`;
   applying `β.symm` is exactly the node's composite using `α.symm`.
-/
theorem exists_etale_lift_isIdempotentElem
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (I : Ideal A)
    [Algebra A B] [Algebra.IsIntegral A B]
    (ebar : B ⧸ I.map (algebraMap A B)) (hebar : IsIdempotentElem ebar) :
    ∃ (A' : CommRingCat.{u}) (g : CommRingCat.of A ⟶ A'),
      letI : Algebra A A' := g.hom.toAlgebra;
      Etale (Spec.map g) ∧
      ∃ α : A ⧸ I ≃+* A' ⧸ I.map (algebraMap A A'),
        (∀ a : A, α (Ideal.Quotient.mk I a) =
          Ideal.Quotient.mk _ (algebraMap A A' a)) ∧
        ∃ (e' : TensorProduct A B (A' : Type u)), IsIdempotentElem e' ∧
          ∃ β : B ⧸ I.map (algebraMap A B) ≃+*
              (TensorProduct A B (A' : Type u)) ⧸
                I.map (algebraMap A (TensorProduct A B (A' : Type u))),
            (∀ b : B, β (Ideal.Quotient.mk _ b) =
              Ideal.Quotient.mk _
                (Algebra.TensorProduct.includeLeftRingHom (R := A) (B := A') b)) ∧
            β ebar = Ideal.Quotient.mk _ e' := by
  sorry

end AlgebraicGeometry
