/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.RingTheory.AssociatedGradedRing
public import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Ring structure of the associated graded of an ideal

Source: Stacks Project, Algebra, proof of Lemma 05GH (`lemma-completion-Noetherian`)
and Section 00JL (`section-graded`); Artin approximation, Section 07XA
(blueprint: lem-weil-pbc-associated-graded-ring-structure).

The pieces, their bilinear multiplication, the direct-sum commutative ring, and the
quotient-algebra structure are those already constructed in `AssociatedGradedRing`.
The theorem records their representative formulas, uniqueness, convolution, and the
injective degree-zero inclusion. No alternative ring or scalar action is chosen.
-/

@[expose] public section

universe u

namespace Ideal

/-- The ring and quotient-algebra structure of the associated graded ring, as used in
Stacks, Algebra, proof of Lemma 05GH and Section 00JL
(blueprint: lem-weil-pbc-associated-graded-ring-structure).

The multiplication `associatedGradedMul` is an `A`-bilinear map. The types in this
statement carry the existing direct-sum `CommRing` and `A/J`-algebra instances, whose
addition is the componentwise addition and whose product is this multiplication.

Proof plan (the ten steps of the node):
1. Ideal powers decrease, and `J^1 = J`, identifying the degree-zero quotient.
2. Expand ideal products to show `J^n J^m` lies in `J^(n+m)`, including zero indices.
3. Changing representatives adds `ub + av + uv` in the next power. Quotient
   surjectivity gives the unique map with the representative formula.
4. Ring distributivity and scalar multiplication on representatives give bilinearity;
   associativity, commutativity and the unit identity descend to the quotients.
5. Convolution has finite support, contained in the sums of the two finite supports;
   multiplying two single-component families gives the homogeneous product formula.
6. Distribute the finite component sums to prove distributivity, and swap the two
   indices for commutativity.
7. Reindex both iterated products by triples of degrees and use associativity on
   representatives to prove associativity of convolution.
8. Only the summand with degree-zero unit survives, proving both unit laws.
9. Degree zero is `A/J`; its inclusion preserves addition, multiplication and one,
   and taking the zero component proves injectivity.
10. The scalar action is multiplication through that ring homomorphism. The formula
    on representatives proves each homogeneous image is closed under scalars;
    componentwise addition and negation give the submodule assertion.
All steps use the quotient module, direct sum, and ideal product definitions cited
in the node, together with elementary ring identities. -/
theorem associatedGraded_ring_structure {A : Type u} [CommRing A] (J : Ideal A) :
    (∀ n m : ℕ,
      (∀ (a : (J ^ n : Ideal A)) (b : (J ^ m : Ideal A)),
        associatedGradedMul J n m (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
          associatedGradedMulAux J n m a b) ∧
      (∀ μ : associatedGradedPiece J n → associatedGradedPiece J m →
          associatedGradedPiece J (n + m),
        (∀ (a : (J ^ n : Ideal A)) (b : (J ^ m : Ideal A)),
          μ (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
            associatedGradedMulAux J n m a b) →
        μ = fun x y ↦ associatedGradedMul J n m x y)) ∧
    (∀ (ξ η : associatedGraded J) (k : ℕ),
      (ξ * η) k = ∑ p ∈ Finset.antidiagonal k,
        if h : p.1 + p.2 = k then
          h ▸ associatedGradedMul J p.1 p.2 (ξ p.1) (η p.2) else 0) ∧
    (∀ (n m : ℕ) (x : associatedGradedPiece J n) (y : associatedGradedPiece J m),
      DirectSum.of (associatedGradedPiece J) n x * DirectSum.of (associatedGradedPiece J) m y =
        DirectSum.of (associatedGradedPiece J) (n + m) (associatedGradedMul J n m x y)) ∧
    (∃ e : (A ⧸ J) ≃+ associatedGradedPiece J 0,
      (∀ a : A, e (Ideal.Quotient.mk J a) =
        Submodule.Quotient.mk (⟨a, by simp⟩ : (J ^ 0 : Ideal A))) ∧
      (∀ a : A ⧸ J, algebraMap (A ⧸ J) (associatedGraded J) a =
        DirectSum.of (associatedGradedPiece J) 0 (e a)) ∧
      (1 : associatedGraded J) = DirectSum.of (associatedGradedPiece J) 0 (e 1)) ∧
    Function.Injective (algebraMap (A ⧸ J) (associatedGraded J)) ∧
    (∀ (a : A) (n : ℕ) (x : (J ^ n : Ideal A)),
      algebraMap (A ⧸ J) (associatedGraded J) (Ideal.Quotient.mk J a) *
          DirectSum.of (associatedGradedPiece J) n (Submodule.Quotient.mk x) =
        DirectSum.of (associatedGradedPiece J) n (Submodule.Quotient.mk (a • x))) ∧
    (∀ n : ℕ, ∃ S : Submodule (A ⧸ J) (associatedGraded J),
      (S : Set (associatedGraded J)) = Set.range (DirectSum.of (associatedGradedPiece J) n)) := by
  sorry

end Ideal
