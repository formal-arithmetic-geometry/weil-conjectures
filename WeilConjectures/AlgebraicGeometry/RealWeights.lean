/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RealWeilSheaves
public import WeilConjectures.AlgebraicGeometry.CondensedWeilReality
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights

/-! # Local weights and reality

Source: latest blueprint, sec-purity-real-sheaves/sk-d-real-weights, local polynomial
and logarithmic-weight complement (blueprint: sk-d-real-weights).

The accepted DAG statement uses a pointwise upper bound. The latest blueprint calls
this a punctual bound, distinguishing it from the finite-filtration mixed bound.
The constructible clauses use the actual scalar stalk and canonical local return of
`CondensedWeil`, rather than a lisse representation on a single global fibre.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace RealSheaves.LocalWeights

variable {K : Type u} [Field K] [Finite K] {C₀ : Scheme.{u}}
  {p : C₀ ⟶ Spec (.of K)} [IsCurve p]
  (W : WeilGroup p) {E : Type v} [Field E]
  {V : Type w} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  (ρ : Representation E W.carrier V)

/-- The local determinant polynomial, allowing the coefficient closure and vector space
in independent universes. Source: latest blueprint, local polynomial complement
(blueprint: sk-d-real-weights). -/
def localPolynomial (x : C₀.finitePoints) : Polynomial E :=
  (ρ (W.frobenius x)).charpolyRev

/-- Local eigenvalues repeated with their algebraic root multiplicities.
Source: latest blueprint, local polynomial complement (blueprint: sk-d-real-weights). -/
def localEigenvalues (x : C₀.finitePoints) : Multiset E :=
  (ρ (W.frobenius x)).charpoly.roots

variable (ι : E →+* ℂ)

/-- Every local eigenvalue has the prescribed logarithmic weight.
Source: latest blueprint, punctual purity and logarithmic-weight complement
(blueprint: sk-d-real-weights). -/
def IsPunctuallyPure (w : ℝ) : Prop :=
  ∀ x : C₀.finitePoints, ∀ α ∈ localEigenvalues W ρ x,
    WeilGroup.frobeniusWeight ι (C₀.pointNorm x.1) α = w

/-- The pointwise upper bound of the accepted node, called a punctual bound in the
latest blueprint. Source: latest blueprint, punctual-bound paragraph and logarithmic
complement (blueprint: sk-d-real-weights). -/
def HasWeightsAtMost (w : ℝ) : Prop :=
  ∀ x : C₀.finitePoints, ∀ α ∈ localEigenvalues W ρ x,
    WeilGroup.frobeniusWeight ι (C₀.pointNorm x.1) α ≤ w

/-- Reality is imposed on every coefficient of each local polynomial.
Source: latest blueprint def-wf-iota-real.md, local polynomial reality; accepted DAG
statement of sk-d-real-weights (blueprint: sk-d-real-weights). -/
def IsReal : Prop :=
  ∀ (x : C₀.finitePoints) (n : ℕ),
    (starRingEnd ℂ) (ι ((localPolynomial W ρ x).coeff n)) =
      ι ((localPolynomial W ρ x).coeff n)

/-- Local Frobenius eigenvalues are nonzero and are precisely the reciprocal roots,
with the multiplicities supplied by the characteristic-polynomial root multiset.
Source: latest blueprint, local polynomial complement (blueprint: sk-d-real-weights).
Proof: the characteristic polynomial is monic and splits over the algebraically
closed coefficient field. The group representation makes Frobenius invertible, so
its determinant and hence the constant characteristic coefficient are nonzero.
Factor the characteristic polynomial into its linear root factors, with multiplicity,
and reverse them to obtain the factors 1-alpha*T. Substitution of alpha inverse
shows the root assertion. Inversion is injective on the nonzero roots, so their
multiplicities agree. In rank zero the product is empty and equals one. -/
theorem local_spectral_data [IsAlgClosed E] (x : C₀.finitePoints) :
    localPolynomial W ρ x =
      ((localEigenvalues W ρ x).map fun α ↦ 1 - Polynomial.C α * Polynomial.X).prod ∧
    ∀ α ∈ localEigenvalues W ρ x,
      α ≠ 0 ∧ (localPolynomial W ρ x).IsRoot α⁻¹ ∧
        Polynomial.rootMultiplicity α⁻¹ (localPolynomial W ρ x) =
          Polynomial.rootMultiplicity α (ρ (W.frobenius x)).charpoly := by
  sorry

/-- The local factor is independent of the representative of local Frobenius.
Source: latest blueprint, local Frobenius convention (blueprint: sk-d-real-weights).
Proof: applying the representation to a conjugacy identifies the two operators by
an invertible change of basis. Their matrices in corresponding bases coincide, so
the basis-independent reverse characteristic polynomials coincide. -/
theorem localPolynomial_eq_of_isConj (x : C₀.finitePoints) (g : W.carrier)
    (hg : IsConj (W.frobenius x) g) :
    localPolynomial W ρ x = (ρ g).charpolyRev := by
  sorry

/-- Reality is equivalent to conjugation stability of the complex eigenvalue multiset.
Source: accepted DAG reality clause, and latest blueprint def-wf-iota-real.md
(blueprint: sk-d-real-weights).
Proof: apply the embedding to the product of factors 1-alpha*T and conjugate its
coefficients. Real coefficients are exactly those fixed by conjugation. Unique
factorization of the two constant-one polynomials identifies their multisets of
nonzero reciprocal roots, including multiplicities. Conversely equal multisets
have equal products. Apply this at every closed point. -/
theorem isReal_iff_conjugation [IsAlgClosed E] :
    IsReal W ρ ι ↔ ∀ x : C₀.finitePoints,
      ((localEigenvalues W ρ x).map ι).map (starRingEnd ℂ) =
        (localEigenvalues W ρ x).map ι := by
  sorry

end RealSheaves.LocalWeights

namespace WeilConjectures.CondensedWeil

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The pointwise logarithmic upper bound on the actual constructible scalar stalks.
Source: latest blueprint, punctual-bound paragraph and local-weight complement;
accepted DAG pointwise-bound clause (blueprint: sk-d-real-weights). -/
def HasPunctualWeightsAtMost (M : WeilModule D l X₀) (ι : PadicAlgCl l →+* ℂ)
    (w : ℝ) : Prop :=
  ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : PadicAlgCl l),
    Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α →
      WeilGroup.frobeniusWeight ι (Nat.card (X₀.left.residueField x.val)) α ≤ w

/-- The existing modulus purity predicate is exactly logarithmic punctual purity.
Source: latest blueprint, purity formula and local-weight complement
(blueprint: sk-d-real-weights).
Proof: the actual local operator is a composite of isomorphisms, so each eigenvalue
is nonzero. Its image under the field embedding has positive norm. A closed point
of a finite-type scheme over the finite field has residue cardinality at least two.
Taking logarithms of the modulus equality gives 2*log(norm)/log(q_x)=w, and
exponentiation reverses the calculation. Quantify over the same closed points,
compatible residue embeddings, and eigenvalues as the existing Pure predicate. -/
theorem pure_iff_logarithmic (M : WeilModule D l X₀) (ι : PadicAlgCl l →+* ℂ)
    (w : ℝ) :
    Pure D l X₀ M ι w ↔
      ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (i : X₀.left.residueField x.val →+* D.k)
        (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
        (α : PadicAlgCl l),
        Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α →
          WeilGroup.frobeniusWeight ι (Nat.card (X₀.left.residueField x.val)) α = w := by
  sorry

/-- The existing polynomial reality predicate is conjugation stability with multiplicity
in every finite basis of the actual scalar stalk. Constructible stalks have such bases.
Source: accepted DAG reality equivalence and constructible-stalk clause; latest
blueprint def-wf-iota-real.md (blueprint: sk-d-real-weights).
Proof: in each finite basis the canonical local return is invertible. Its characteristic
polynomial splits with nonzero roots over the algebraically closed coefficient field.
Reverse the factorization, embed in the complex numbers, and conjugate. The
coefficients have zero imaginary part exactly when conjugation fixes the polynomial.
Uniqueness of its nonzero reciprocal roots, with multiplicities, proves the forward
implication, and multiplying the conjugate-stable multiset proves the converse.
The existing Real predicate already quantifies over exactly these finite bases. -/
theorem real_iff_conjugation (M : WeilModule D l X₀) (ι : PadicAlgCl l →+* ℂ) :
    Real D l X₀ M ι ↔
      ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (i : X₀.left.residueField x.val →+* D.k)
        (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
        (n : ℕ) (b : Module.Basis (Fin n) (PadicAlgCl l) (closedFiber D l X₀ M x i hi)),
        (((LinearMap.toMatrix b b (closedOperator D l X₀ M x i hi).hom).charpoly.roots.map
          ι).map (starRingEnd ℂ)) =
          (LinearMap.toMatrix b b (closedOperator D l X₀ M x i hi).hom).charpoly.roots.map
            ι := by
  sorry

end WeilConjectures.CondensedWeil
