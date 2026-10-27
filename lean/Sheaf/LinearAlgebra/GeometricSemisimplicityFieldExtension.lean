module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Geometric semisimplicity and extension of the ground field

Source: Milne, Algebraic Groups (2017), Section 9(b), printed pp.166,168; the supporting
invariant-complement and arbitrary-extension arguments in the DAG
(blueprint: lem-sfb-geometric-semisimplicity-field-extension).

Geometric diagonalizability is written explicitly as existence of an eigenbasis over the
canonical algebraic closure. No perfectness or algebraicity is imposed on the extension field.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Module.End

/-- Over a perfect field, invariant complements, separability of the minimal polynomial,
and an eigenbasis over an algebraic closure are equivalent. The eigenbasis condition is
preserved and reflected by every extension field, including for the zero vector space.
Source: Milne, Algebraic Groups (2017), Section 9(b), printed pp.166,168, and the supporting
linear-algebra argument (blueprint: lem-sfb-geometric-semisimplicity-field-extension).

Proof:
1. For the zero space the scalar extension is zero, the minimal polynomial is one, and the
empty basis is an eigenbasis. Invariant complements exist, so all assertions hold.
2. For a monic polynomial, separability is equivalent to distinct roots in an algebraic
closure: factor it into linear factors (lem-weil-alg-closed-linear-factorization) and use
lem-weil-pbc-distinct-linear-factors-separable. Conversely a repeated linear factor divides
both the polynomial and its derivative, contradicting coprimality. Invariant complements
imply a squarefree minimal polynomial (lem-sfb-complement-semisimple-minpoly-squarefree).
Perfectness identifies squarefreeness and separability
(lem-sfb-perfect-polynomial-squarefree-separable). Conversely the squarefree minimal
polynomial annihilates the operator, giving invariant complements by
lem-sfb-squarefree-annihilator-invariant-complements.
3. Over any field, not necessarily perfect, extend to an algebraic closure. The minimal
polynomial is obtained by mapping coefficients (lem-sfb-endomorphism-minpoly-scalar-extension),
and separability survives this map (lem-sfb-polynomial-separability-field-map). The extended
operator has invariant complements by the squarefree-annihilator lemma, and its eigenspaces
span by lem-sfb-invariant-complements-eigenspace-span. Choose a finite spanning set of
eigenvectors and remove dependent vectors to obtain an eigenbasis.
4. Conversely, for an eigenbasis take the product of X minus the distinct eigenvalues.
This separable polynomial annihilates the operator. Euclidean division shows its minimal
polynomial divides that product, hence is separable by
lem-weil-pbc-distinct-linear-factors-separable. The scalar-extension minimal-polynomial lemma
and lem-sfb-polynomial-separability-field-map reflect separability to the original field.
This proves the geometric criterion over every field.
5. For an arbitrary extension L/k, its extended minimal polynomial is the coefficient image
of the original one. Separability is preserved and reflected by this field map. Applying
steps 3 and 4 over both fields proves the last equivalence. No assumption that L is perfect,
algebraic, or that the operator is invertible is needed. -/
theorem geometricSemisimplicity_fieldExtension
    {k : Type u} [Field k] [PerfectField k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (T : Module.End k V) (L : Type w) [Field L] [Algebra k L] :
    (T.IsSemisimple ↔ (minpoly k T).Separable) ∧
    ((minpoly k T).Separable ↔
      ∃ (n : ℕ) (b : Module.Basis (Fin n) (AlgebraicClosure k)
          (AlgebraicClosure k ⊗[k] V)) (μ : Fin n → AlgebraicClosure k),
        ∀ i : Fin n,
          Module.End.HasEigenvector (T.baseChange (AlgebraicClosure k)) (μ i) (b i)) ∧
    ((∃ (n : ℕ) (b : Module.Basis (Fin n) (AlgebraicClosure L)
          (AlgebraicClosure L ⊗[L] (L ⊗[k] V))) (μ : Fin n → AlgebraicClosure L),
        ∀ i : Fin n,
          Module.End.HasEigenvector
            ((T.baseChange L).baseChange (AlgebraicClosure L)) (μ i) (b i)) ↔
      ∃ (n : ℕ) (b : Module.Basis (Fin n) (AlgebraicClosure k)
          (AlgebraicClosure k ⊗[k] V)) (μ : Fin n → AlgebraicClosure k),
        ∀ i : Fin n,
          Module.End.HasEigenvector (T.baseChange (AlgebraicClosure k)) (μ i) (b i)) := by
  sorry

end Module.End
