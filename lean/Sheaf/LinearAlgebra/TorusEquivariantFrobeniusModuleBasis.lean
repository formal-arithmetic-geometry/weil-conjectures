module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.SkewPolynomial.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Basis.Defs

/-! # Homogeneous bases of Frobenius skew-polynomial modules

Source: agent-formulated graded algebra input for Conrad--Lichtenstein, Linear Algebraic
Groups I, Appendix D.3, proof of Theorem D.3.2, printed p.86; ungraded freeness input:
Milne, Algebraic Groups (2017), Proposition 14.50, printed p.296
(blueprint: lem-sfb-torus-equivariant-frobenius-module-basis).

The Mathlib skew-polynomial twist is specified to be Frobenius. Subspaces use the
restriction of scalars along `SkewPolynomial.CRingHom`, the constant-polynomial map.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace SkewPolynomial

/-- A finite free left Frobenius skew-polynomial module with a lattice-weight decomposition
has a homogeneous basis of the same size, over any field of prime characteristic.

Source: agent-formulated homogeneous refinement for Conrad--Lichtenstein, Linear Algebraic
Groups I, Appendix D.3, proof of Theorem D.3.2, printed p.86, with Milne, Algebraic Groups
(2017), Proposition 14.50, printed p.296 as the ungraded freeness input
(blueprint: lem-sfb-torus-equivariant-frobenius-module-basis).

The twist equality `hφ` makes Mathlib's multiplication
`(a F^r)(b F^t) = a φ^[r](b) F^(r+t)` precisely the stated Frobenius multiplication.
The subspaces are taken for the actual restricted scalar structure, not an independent
vector-space action. No perfectness assumption is made, and `d = 0`, `s = 0`, and zero
weights are allowed.

Proof plan:
1. Split off the weight-zero component. Multiplication of lattice weights by the prime
   is injective, so both this component and the sum of the nonzero-weight components
   are left submodules. Projecting the given finite basis makes both finitely generated.
   Apply lem-sfb-frobenius-skew-free-submodules to get finite bases of both summands.
   The basis of the weight-zero summand is already homogeneous.
2. For the other summand N, put J = span_k F(N). In a free basis e_i, J has coefficient
   basis F^q e_i for q >= 1, so N/J has dimension equal to the size of that basis.
   Decomposing inputs into their weights shows J is graded. Decompose a finite spanning
   set of N/J into its finitely many homogeneous parts, choose bases in those weight
   components, and lift them homogeneously to b_j in N.
3. Apply lem-sfb-dilating-weight-nakayama to N and T = F. Its zero-weight component is
   zero, T is Frobenius-semilinear, and it multiplies weights by p. The chosen cosets
   span N/J, so all F^q b_j span N over k, equivalently the b_j generate N over the
   skew-polynomial ring.
4. In the given free-module coordinates, F shifts the polynomial degree and applies
   coefficientwise Frobenius. Frobenius is injective over a field. Thus
   lem-sfb-coefficient-endomorphism-preserves-independence shows that F preserves
   independence of finite k-families; the coordinate shift preserves it as well.
5. Induct on the largest exponent in a relation among the F^q b_j. Reduction modulo J
   kills the exponent-zero coefficients, and step 4 kills the rest by induction.
   Every finite skew-polynomial relation expands into such a relation, so the b_j
   form a free basis. Concatenate with the weight-zero basis. For any finite free
   basis, its cosets form a k-basis of M/span_k F(M), by the coefficient calculation
   of step 2. Comparison with the given basis forces the concatenated size to be d.
   Reindex by Fin d and retain the weights. Empty bases and the singleton lattice
   when s = 0 are included. -/
theorem exists_homogeneous_basis_of_frobenius_weights
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    [MulSemiringAction (Multiplicative ℕ) k]
    (hφ : SkewPolynomial.φ (R := k) = frobenius k p)
    {M : Type v} [AddCommGroup M] [Module (SkewPolynomial k) M]
    (d s : ℕ) (hfree : Nonempty (M ≃ₗ[SkewPolynomial k] (Fin d → SkewPolynomial k)))
    (W : (Fin s → ℤ) → @Submodule k M _ _ (Module.compHom M SkewPolynomial.CRingHom))
    (hW : DirectSum.IsInternal W)
    (hF : ∀ (ν : Fin s → ℤ) (m : M), m ∈ W ν →
      (SkewPolynomial.X : SkewPolynomial k) • m ∈ W (p • ν)) :
    ∃ (b : Module.Basis (Fin d) (SkewPolynomial k) M) (ν : Fin d → (Fin s → ℤ)),
      ∀ j : Fin d, b j ∈ W (ν j) := by
  sorry

end SkewPolynomial
