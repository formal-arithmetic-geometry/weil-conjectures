/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FiniteType
import Sheaf.AlgebraicGeometry.IntegralClosureFiniteFibreChooseG
import Sheaf.AlgebraicGeometry.IntegralClosureFiniteFibreImageClopen
import Sheaf.RingTheory.FiniteQuotientComponentQuasiFinite
import Sheaf.RingTheory.ZariskisMainAway

/-!
# Integral-closure localization of a finite fibre component

Source: Stacks Project, `more-algebra.tex`, Lemma 09XH;
blueprint: `lem-weil-pbc-integral-closure-finite-fibre-part-localization`.
-/

@[expose] public section

universe u v w z

/-- The finite component of a fibre of a finite-type algebra is obtained from the
integral closure, and the two algebras agree after inverting one element.

Source: Stacks Project, `more-algebra.tex`, Lemma 09XH;
(blueprint: lem-weil-pbc-integral-closure-finite-fibre-part-localization).
Proof:
1. The finite A/I-algebra C₁ makes A → B quasi-finite at each prime of
   T = Spec C₁, by lem-weil-pbc-integral-closure-finite-fibre-quasi-finite.
2. At each such prime affine Zariski Main gives an element of B' whose
   localization map is an isomorphism. Their principal opens form U, containing
   T in its inverse image, by lem-weil-pbc-integral-closure-zariski-main-away.
3. The image of T is open in the closed fibre using the isomorphism over U,
   and closed by finiteness. Its clopen decomposition yields ε', preservation
   of both factors, and the first-factor isomorphism, by
   lem-weil-pbc-integral-closure-finite-fibre-image-clopen.
4. Separate the two closed factors and the complement of U to choose g lifting
   ε' with D(g) contained in U. The comparison of local rings gives bijectivity
   of the induced localization map, by lem-weil-pbc-integral-closure-finite-fibre-choose-g.
5. The product idempotent identifies the first ideal with C₁ via q and e:
   every c has exactly one preimage fixed by ε'. The complementary ideal maps
   to C₂, giving precisely the requested compatible decomposition.
-/
theorem integralClosure_finiteFibrePart_localization
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B]
    (I : Ideal A)
    (C₁ : Type w) (C₂ : Type z) [CommRing C₁] [CommRing C₂]
    [Algebra (A ⧸ I) C₁] [Algebra (A ⧸ I) C₂]
    [Module.Finite (A ⧸ I) C₁]
    (e : (B ⧸ Ideal.map (algebraMap A B) I) ≃+* (C₁ × C₂))
    (he : ∀ a : A, e (Ideal.Quotient.mk _ (algebraMap A B a)) =
      (algebraMap (A ⧸ I) C₁ (Ideal.Quotient.mk I a),
       algebraMap (A ⧸ I) C₂ (Ideal.Quotient.mk I a)))
    (ε : B ⧸ Ideal.map (algebraMap A B) I)
    (hε : e ε = (1, 0)) :
    ∃ (ε' : (integralClosure A B) ⧸
          Ideal.map (algebraMap A (integralClosure A B)) I)
      (g : integralClosure A B)
      (q : (integralClosure A B) ⧸
          Ideal.map (algebraMap A (integralClosure A B)) I →+*
          (B ⧸ Ideal.map (algebraMap A B) I)),
      (∀ x : integralClosure A B,
        q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x.1) ∧
      IsIdempotentElem ε' ∧ q ε' = ε ∧
      (∀ x, ε' * x = x → (e (q x)).2 = 0) ∧
      (∀ x, (1 - ε') * x = x → (e (q x)).1 = 0) ∧
      (∀ c : C₁, ∃! x, ε' * x = x ∧ e (q x) = (c, 0)) ∧
      Ideal.Quotient.mk _ g = ε' ∧
      Function.Bijective (Localization.awayMap (integralClosure A B).val.toRingHom g) := by
  sorry
