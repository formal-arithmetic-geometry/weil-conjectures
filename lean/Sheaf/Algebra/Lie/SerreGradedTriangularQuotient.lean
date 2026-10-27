module

public import Mathlib.Algebra.Lie.SerreConstruction
public import Mathlib.Algebra.DirectSum.Module

/-!
# Graded triangular decomposition of the generalized Serre quotient

Source: Milne, Algebraic Groups (2017), Theorem 23.63, first proof, p.504,
and the characteristic-zero extension p.508.
(blueprint: lem-sfb-serre-graded-triangular-quotient)

The ambient algebra is Mathlib's presented quotient. The auxiliary definitions name
its generator classes and the Serre ideal in a free algebra on just one family.
The two half-algebra identifications below preserve their specified generators;
the triangular decomposition is a vector-space decomposition.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace LieAlgebra

/-- The actual generator class in the generalized Serre quotient, for any index type.
Source: Milne, Algebraic Groups, Theorem 23.63, first proof, p.504.
(blueprint: lem-sfb-serre-graded-triangular-quotient) -/
noncomputable def generalizedSerreGenerator {I : Type u} [DecidableEq I]
    (A : Matrix I I ℤ) (g : CartanMatrix.Generators I) : Matrix.ToLieAlgebra ℚ A :=
  LieSubmodule.Quotient.mk' (CartanMatrix.Relations.toIdeal ℚ A) (FreeLieAlgebra.of ℚ g)

/-- The ideal generated solely by the Serre relations in a free rational Lie algebra
on one family. This same presentation is used for the positive and negative halves.
Source: Milne, Algebraic Groups, Theorem 23.63, first proof, p.504.
(blueprint: lem-sfb-serre-graded-triangular-quotient) -/
noncomputable def serreHalfIdeal {I : Type u} (A : Matrix I I ℤ) :
    LieIdeal ℚ (FreeLieAlgebra ℚ I) :=
  LieSubmodule.lieSpan ℚ (FreeLieAlgebra ℚ I)
    {s | ∃ (i j : I), i ≠ j ∧ s =
      ((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ I) (FreeLieAlgebra.of ℚ i)) ^
        (1 - A i j).toNat) (FreeLieAlgebra.of ℚ j)}

/-- The generalized Cartan Serre quotient has its generator grading, independent
Cartan space, two Serre-only halves, and triangular vector-space decomposition.
Source: Milne, Algebraic Groups, Theorem 23.63, first proof, p.504, and p.508.
(blueprint: lem-sfb-serre-graded-triangular-quotient)

Proof plan (the seven steps of the node):
1. First impose only the Weyl relations. Apply
   lem-sfb-weyl-relations-free-normal-form to obtain free negative and positive
   subalgebras and the independent Cartan space, for the rational matrix A.
2. Apply lem-sfb-free-lie-homogeneous-presentation-grading with generator degrees
   zero, epsilon_i and -epsilon_i. All Weyl and Serre relations are homogeneous,
   so the Weyl quotient, the Serre quotient and both half ideals inherit gradings.
3. For i != j, D = ad E_i and a = a_ij, Jacobi gives
   [H_i,D^r E_j] = (a+2r) D^r E_j and
   [F_i,D^r E_j] = -r(a+r-1) D^(r-1) E_j. The latter coefficient vanishes at
   r = 1-a. For k outside {i,j} the opposite bracket vanishes immediately.
   For k = j it is -D^(1-a) H_j, zero since D^2 H_j = 0, or, when a = 0,
   since a_ji = 0. Also [H_k,s_ij] = ((1-a_ij)a_ki+a_kj)s_ij.
4. The positive half ideal is the span of iterated ad E_l applied to the Serre
   generators. Its vectors are Cartan eigenvectors. Induction using
   [F_k,[E_l,u]] = -delta_kl [H_k,u]+[E_l,[F_k,u]] proves opposite-generator
   stability, hence it is an ideal of the whole Weyl quotient.
5. The involution H_i -> -H_i, E_i -> F_i, F_i -> E_i preserves the Weyl
   relations and exchanges the half ideals. Their sum is therefore exactly the
   full Serre ideal, and is direct by the Weyl triangular decomposition.
6. Quotient the Weyl decomposition by that sum. The canonical sum map from the
   negative quotient, Cartan space and positive quotient is bijective: its kernel
   is exactly the two half ideals and has zero Cartan coordinate. This gives the
   generator-preserving Lie equivalences and the unique triangular expansion.
7. Positive bracket words have strictly positive total degree, and negative
   words strictly negative total degree. Thus degree zero is precisely Cartan,
   and other nonzero degrees lie in the two coordinate cones. The epsilon_i
   piece is the line E_i; evaluation in the one-dimensional abelian algebra
   detects its nonvanishing before quotienting. Serre generators have total
   degree at least two, so the homogeneous ideal-span formula leaves that line
   untouched. A word of degree n epsilon_i for n > 1 uses only E_i and vanishes
   by alternation and induction on word length. Use the involution for negative
   degrees. With no indices there are no generators, so every space is zero.
-/
theorem serre_graded_triangular_quotient
    (I : Type u) [Fintype I] [DecidableEq I] (A : Matrix I I ℤ)
    (hdiag : ∀ i : I, A i i = 2)
    (hoff : ∀ (i j : I), i ≠ j → A i j ≤ 0)
    (hzero : ∀ (i j : I), A i j = 0 ↔ A j i = 0) :
    ∃ grade : (I → ℤ) → Submodule ℚ (Matrix.ToLieAlgebra ℚ A),
      DirectSum.IsInternal grade ∧
      (∀ (m n : I → ℤ) (x y : Matrix.ToLieAlgebra ℚ A),
        x ∈ grade m → y ∈ grade n → ⁅x, y⁆ ∈ grade (m + n)) ∧
      (∀ i : I, generalizedSerreGenerator A (.H i) ∈ grade 0 ∧
        generalizedSerreGenerator A (.E i) ∈ grade (Pi.single i 1) ∧
        generalizedSerreGenerator A (.F i) ∈ grade (-Pi.single i 1)) ∧
      (∃ c : (I → ℚ) ≃ₗ[ℚ] grade 0,
        ∀ q : I → ℚ, (c q : Matrix.ToLieAlgebra ℚ A) =
          ∑ i : I, q i • generalizedSerreGenerator A (.H i)) ∧
      (∀ m : I → ℤ, grade m ≠ ⊥ → m ≠ 0 →
        (∀ i : I, 0 ≤ m i) ∨ (∀ i : I, m i ≤ 0)) ∧
      (∃
        (p : (FreeLieAlgebra ℚ I ⧸ serreHalfIdeal A) ≃ₗ⁅ℚ⁆
          LieSubalgebra.lieSpan ℚ (Matrix.ToLieAlgebra ℚ A)
            (Set.range fun i : I ↦ generalizedSerreGenerator A (.E i)))
        (n : (FreeLieAlgebra ℚ I ⧸ serreHalfIdeal A) ≃ₗ⁅ℚ⁆
          LieSubalgebra.lieSpan ℚ (Matrix.ToLieAlgebra ℚ A)
            (Set.range fun i : I ↦ generalizedSerreGenerator A (.F i))),
        (∀ i : I,
          (p (LieSubmodule.Quotient.mk' (serreHalfIdeal A) (FreeLieAlgebra.of ℚ i)) :
            Matrix.ToLieAlgebra ℚ A) = generalizedSerreGenerator A (.E i)) ∧
        (∀ i : I,
          (n (LieSubmodule.Quotient.mk' (serreHalfIdeal A) (FreeLieAlgebra.of ℚ i)) :
            Matrix.ToLieAlgebra ℚ A) = generalizedSerreGenerator A (.F i))) ∧
      (∀ x : Matrix.ToLieAlgebra ℚ A, ∃! t :
        (LieSubalgebra.lieSpan ℚ (Matrix.ToLieAlgebra ℚ A)
          (Set.range fun i : I ↦ generalizedSerreGenerator A (.F i))) ×
        (I → ℚ) ×
        (LieSubalgebra.lieSpan ℚ (Matrix.ToLieAlgebra ℚ A)
          (Set.range fun i : I ↦ generalizedSerreGenerator A (.E i))),
        x = (t.1 : Matrix.ToLieAlgebra ℚ A) +
          (∑ i : I, t.2.1 i • generalizedSerreGenerator A (.H i)) +
          (t.2.2 : Matrix.ToLieAlgebra ℚ A)) ∧
      (∀ i : I,
        grade (Pi.single i 1) =
          Submodule.span ℚ {generalizedSerreGenerator A (.E i)} ∧
        generalizedSerreGenerator A (.E i) ≠ 0 ∧
        grade (-Pi.single i 1) =
          Submodule.span ℚ {generalizedSerreGenerator A (.F i)} ∧
        generalizedSerreGenerator A (.F i) ≠ 0) ∧
      (∀ (i : I) (n : ℤ), 1 < |n| → grade (n • Pi.single i 1) = ⊥) ∧
      (IsEmpty I → Subsingleton (Matrix.ToLieAlgebra ℚ A)) := by
  sorry

end LieAlgebra
