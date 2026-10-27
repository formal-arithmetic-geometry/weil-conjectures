module

public import Sheaf.RingTheory.SupportedHomogeneousDivision
public import Mathlib.Algebra.MvPolynomial.Eval
import Sheaf.LinearAlgebra.TriangularChangeOfBasis
import Mathlib.RingTheory.FiniteType

/-! # Supported homogeneous division with extra variables

Source: Bierstone--Milman, Canonical desingularization in characteristic zero,
Lemma 7.7, pp.263--264, degree-by-degree algebraic formulation;
ILO VIII 2.3.11--2.3.13, pp.93--94.
(blueprint: lem-trf-homogeneous-division-extra-variables)

`HasUniqueDivision` expresses that the indexed family is a basis of its homogeneous
component. The vertices in the larger variable set are extended by zero in the new
coordinates. No monotonicity or first-exponent condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MonomialDiagram

/-- Supported homogeneous division is equivalent before and after adjoining extra variables.

Source: Bierstone--Milman, Lemma 7.7, pp.263--264, implication (c) to (a) and converse,
in the degree-by-degree formulation of the node; ILO VIII 2.3.11--2.3.13.
(blueprint: lem-trf-homogeneous-division-extra-variables)

Proof: Assign a quotient index `(i, β)` to `α i + β` and a remainder index to itself.
The least vertex dividing an exponent makes this a degree-preserving bijection with
monomials. The same bijection with the extra exponent retained identifies the larger
index set; its diagram and quotient supports are the products with all extra exponents.
Group each homogeneous polynomial by its extra-variable exponent `μ`. Restricted
unique division gives a basis in every coefficient component, so the unperturbed
family using `H i (0,V)` is a basis. Replacing it by `H i` changes each vector only
by terms of strictly larger extra-variable degree. Ordering these finitely many indices
by that degree gives a triangular matrix with diagonal one. Apply
`Module.Basis.exists_basis_of_triangular_unit_diagonal` to obtain the larger basis.
Conversely specialize a full basis expansion at the extra variables zero. The surviving
vectors are the restricted family, so they span. The monomial index bijection shows
that its matrix is square; the surjective endomorphism of the finite free homogeneous
component is bijective by `OrzechProperty.bijective_of_surjective_endomorphism`.
Thus its coefficients are unique. Empty index sets and degree-zero vertices obey the
same argument, including zero homogeneous generators and zero homogeneous components. -/
theorem hasUniqueDivision_extraVariables_iff
    {L : Type u} [Field L] {m r s : ℕ}
    (α : Fin s → Fin r →₀ ℕ) (hα : Function.Injective α)
    (H : Fin s → MvPolynomial (Fin m ⊕ Fin r) L)
    (hH : ∀ i : Fin s, (H i).IsHomogeneous (α i).degree) :
    (∀ t : ℕ, HasUniqueDivision (generated α) α
      (fun i ↦ MvPolynomial.eval₂Hom MvPolynomial.C
        (Sum.elim (fun _ : Fin m ↦ 0) (MvPolynomial.X : Fin r → MvPolynomial (Fin r) L))
        (H i)) t) ↔
    (∀ t : ℕ, HasUniqueDivision
      (generated (fun i ↦ Finsupp.mapDomain (Sum.inr : Fin r → Fin m ⊕ Fin r) (α i)))
      (fun i ↦ Finsupp.mapDomain (Sum.inr : Fin r → Fin m ⊕ Fin r) (α i)) H t) := by
  sorry

/-- Both supported homogeneous division properties persist under every field extension.
Together with `hasUniqueDivision_extraVariables_iff` over the extension field, this gives
also the equivalence after coefficientwise extension, independently of whether it held
before extension.

Source: Bierstone--Milman, Lemma 7.7, pp.263--264, degree-by-degree formulation,
and the field-extension clause of the node; ILO VIII 2.3.11--2.3.13.
(blueprint: lem-trf-homogeneous-division-extra-variables)

Proof: For each fixed degree, the first-dividing-vertex bijection identifies each family
with the finite monomial basis. A basis family has an invertible square coefficient
matrix. Map this matrix and its inverse coefficientwise through the field embedding;
the two inverse identities are preserved. This proves unique coefficients for each
homogeneous polynomial over the extension field, separately for the restricted family
and the full family. Restriction at the extra variables zero commutes with coefficient
mapping, so the displayed restricted polynomials are exactly the extended restrictions.
The previous theorem over the extension field gives the equivalence there. This uses
no characteristic restriction, monotonicity, first exponent, or nonvanishing assumption. -/
theorem hasUniqueDivision_extraVariables_map
    {L : Type u} [Field L] {E : Type v} [Field E] (f : L →+* E)
    {m r s : ℕ} (α : Fin s → Fin r →₀ ℕ) (hα : Function.Injective α)
    (H : Fin s → MvPolynomial (Fin m ⊕ Fin r) L)
    (hH : ∀ i : Fin s, (H i).IsHomogeneous (α i).degree) :
    ((∀ t : ℕ, HasUniqueDivision (generated α) α
        (fun i ↦ MvPolynomial.eval₂Hom MvPolynomial.C
          (Sum.elim (fun _ : Fin m ↦ 0) (MvPolynomial.X : Fin r → MvPolynomial (Fin r) L))
          (H i)) t) →
      ∀ t : ℕ, HasUniqueDivision (generated α) α
        (fun i ↦ MvPolynomial.map f (MvPolynomial.eval₂Hom MvPolynomial.C
          (Sum.elim (fun _ : Fin m ↦ 0) (MvPolynomial.X : Fin r → MvPolynomial (Fin r) L))
          (H i))) t) ∧
    ((∀ t : ℕ, HasUniqueDivision
        (generated (fun i ↦ Finsupp.mapDomain (Sum.inr : Fin r → Fin m ⊕ Fin r) (α i)))
        (fun i ↦ Finsupp.mapDomain (Sum.inr : Fin r → Fin m ⊕ Fin r) (α i)) H t) →
      ∀ t : ℕ, HasUniqueDivision
        (generated (fun i ↦ Finsupp.mapDomain (Sum.inr : Fin r → Fin m ⊕ Fin r) (α i)))
        (fun i ↦ Finsupp.mapDomain (Sum.inr : Fin r → Fin m ⊕ Fin r) (α i))
        (fun i ↦ MvPolynomial.map f (H i)) t) := by
  sorry

end MonomialDiagram
