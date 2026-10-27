module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.RingTheory.HomogeneousMaximalGradedFieldQuotient

/-! # Opposite-degree products from the graded stabilizer ideal

Source: Stacks Project, Groupoids, Tag 0EKK (lemma-complete-reducibility-Gm),
for the grading interpretation; independent augmentation-ideal argument of Q20,
refined by Q112 in the DAG proof.
(blueprint: lem-sfb-graded-stabilizer-strong-products)

The coefficient grading is independent of the formal exponents in `AddMonoidAlgebra A M`.
The two generating sets are written directly with `Ideal.span`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace GradedRing

/-- If the homogeneous stabilizer ideal equals the full augmentation ideal, each pair of
opposite degrees admits finitely many products summing to one. `Fin 0` permits the empty sum.

Source: Stacks Project, Groupoids, Tag 0EKK (lemma-complete-reducibility-Gm), grading context
only; independent Q20 augmentation-ideal argument, refined by Q112 in the DAG proof.
(blueprint: lem-sfb-graded-stabilizer-strong-products)

Proof:
1. Fix m. In the zero ring use the empty sum. Otherwise let B = A_0 and let K be the ideal
   of B consisting of finite sums of products from A_m and A_(-m). If 1 is not in K, the
   extended ideal L = KA is proper and homogeneous: its degree-n component is a sum of
   elements k_i (x_i)_n, and its degree-zero component is contained in K.
2. Apply Ideal.exists_homogeneous_maximal_gradedField_quotient
   [lem-sfb-homogeneous-maximal-graded-field-quotient] to L. Obtain a proper homogeneous
   ideal H containing L and a nonzero graded quotient D = A/H in which every nonzero
   homogeneous element has an inverse in the opposite degree.
3. The support N = {n : D_n is nonzero} is a subgroup of M. It contains zero because
   1 is nonzero; inverses give closure under negation, and products of units give
   closure under addition.
4. Map A[M] to D[M/N] by sending a coefficient c to its quotient q(c), and t^r to u^(r+N).
   Each stabilizer generator maps to zero: either q(a) = 0 or its degree lies in N.
   The assumed equality of ideals therefore kills every t^r - 1. If r is outside N,
   the coefficient of u^(r+N) in its image is 1, a contradiction. Hence N = M.
5. Choose a nonzero d in D_m and an opposite-degree inverse e. Lift them to a in A_m
   and b in A_(-m). Then ab lies in K, hence in L and H. The quotient-kernel assertion
   [def-weil-pbc-algebra-hom-quotient] gives de = 0, contradicting de = 1 in the nonzero
   quotient. Thus 1 belongs to K, giving the finite sum claimed. -/
theorem exists_sum_mul_eq_one_of_stabilizer_eq_augmentation
    {M : Type u} [AddCommGroup M] [DecidableEq M] {A : Type v} [CommRing A]
    (𝒜 : M → AddSubgroup A) [GradedRing 𝒜]
    (hIdeals :
      Ideal.span {x : AddMonoidAlgebra A M | ∃ (m : M) (a : 𝒜 m),
        x = AddMonoidAlgebra.single 0 (a : A) * (AddMonoidAlgebra.single m 1 - 1)} =
      Ideal.span (Set.range (fun m : M ↦
        (AddMonoidAlgebra.single m 1 - 1 : AddMonoidAlgebra A M)))) :
    ∀ m : M, ∃ (n : ℕ) (a : Fin n → 𝒜 m) (b : Fin n → 𝒜 (-m)),
      ∑ j : Fin n, (a j : A) * (b j : A) = 1 := by
  sorry

end GradedRing
