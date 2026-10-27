module

public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.RingDivision

/-! # A graded polynomial with nonzero vertex image is regular

Source: the agent-written graded coefficient and linear substitution calculation in the DAG;
Stacks Project, Algebra, Tag 07BV, proof of lemma-colimit-syntomic, supports only the final
monic regularity step (blueprint: lem-trf-graded-polynomial-vertex-regularity).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MvPolynomial

/-- A homogeneous polynomial with nonzero vertex image becomes monic in a linear direction.
There are `e + 1` variables, indexed starting at zero. The coefficient criterion `hf` is
homogeneity for the total grading that combines the grading of B with variable degree one.
The equation `hH` names the canonical reduction H without choosing an inverse to the
identification of the degree-zero subring with k: after embedding its coefficients in B,
H is the coefficientwise degree-zero projection of f. Nontriviality of B expresses the
inclusion k = B_0. The equivalence clause says that the substitution is graded, and
`finSuccEquiv` collects powers of the distinguished variable X 0.

Source: the agent-written refinement, steps 1--5 of the DAG node, with Stacks Project,
Algebra, Tag 07BV, proof of lemma-colimit-syntomic, supporting monic regularity only
(blueprint: lem-trf-graded-polynomial-vertex-regularity).

Proof:
1. Expand f in monomials. The coefficient at d has degree n - d.degree and is zero
   when d.degree > n. Projection to degree zero kills all coefficients with
   d.degree < n and fixes the scalar coefficients of variable degree n. Thus H is
   a nonzero homogeneous form of degree n over k.
2. Apply lem-trf-infinite-field-top-form-direction, represented by
   MvPolynomial.funext_set, to choose v nonzero with c = H(v) nonzero. Choose r
   with v_r nonzero and complete v by the coordinate vectors other than the r-th.
3. The resulting matrix M is invertible: if its other columns are e_i, the inverse
   sends y to first coordinate v_r^{-1} y_r and remaining coordinates
   y_i - v_i v_r^{-1} y_r. The polynomial universal property gives substitution
   by M, and substitution by its inverse is the inverse map. Both preserve total
   degree because each variable image has degree one and B is fixed.
4. Collect powers of X 0 using finSuccEquiv. Every substituted monomial has
   X 0 degree at most n. Only variable-degree-n monomials can contribute to the
   coefficient of (X 0)^n. Their contribution is the scalar sum b_d v^d = H(v).
   Consequently the polynomial has degree exactly n and leading coefficient c;
   multiplication by c^{-1} makes it monic.
5. Apply lem-weil-pbc-monic-polynomial-nonzerodivisor, represented by
   Polynomial.Monic.mem_nonZeroDivisors, over D = B[the remaining variables].
   If f*g = 0, substitution and rescaling give q*sigma(g) = 0 with q monic.
   Therefore sigma(g) = 0 and g = 0. Apply this to g-h to obtain injectivity
   of multiplication by f. -/
theorem exists_monic_linear_direction_of_vertex_ne_zero
    {k : Type u} [Field k] [Infinite k]
    {B : Type v} [CommRing B] [Nontrivial B] [Algebra k B]
    (𝒜 : ℕ → Submodule k B) [GradedAlgebra 𝒜] [GradedAlgebra.IsStandard 𝒜]
    (e n : ℕ) (hn : 1 ≤ n) (f : MvPolynomial (Fin (e + 1)) B)
    (hf : ∀ d : Fin (e + 1) →₀ ℕ,
      coeff d f ∈ 𝒜 (n - d.degree) ∧ (n < d.degree → coeff d f = 0))
    (H : MvPolynomial (Fin (e + 1)) k)
    (hH : map (algebraMap k B) H = map (GradedRing.projZeroRingHom 𝒜) f)
    (hH0 : H ≠ 0) :
    (∃ (v : Fin (e + 1) → k) (M : Matrix.GeneralLinearGroup (Fin (e + 1)) k)
        (σ : MvPolynomial (Fin (e + 1)) B ≃ₐ[B] MvPolynomial (Fin (e + 1)) B),
      v ≠ 0 ∧ eval v H ≠ 0 ∧
      (∀ i : Fin (e + 1), (M : Matrix (Fin (e + 1)) (Fin (e + 1)) k) i 0 = v i) ∧
      (∀ i : Fin (e + 1), σ (X i) =
        ∑ j : Fin (e + 1),
          C (algebraMap k B ((M : Matrix (Fin (e + 1)) (Fin (e + 1)) k) i j)) * X j) ∧
      (∀ (m : ℕ) (g : MvPolynomial (Fin (e + 1)) B),
        (∀ d : Fin (e + 1) →₀ ℕ,
          coeff d g ∈ 𝒜 (m - d.degree) ∧ (m < d.degree → coeff d g = 0)) ↔
        (∀ d : Fin (e + 1) →₀ ℕ,
          coeff d (σ g) ∈ 𝒜 (m - d.degree) ∧ (m < d.degree → coeff d (σ g) = 0))) ∧
      (finSuccEquiv B e (σ f)).natDegree = n ∧
      (finSuccEquiv B e (σ f)).leadingCoeff = C (algebraMap k B (eval v H)) ∧
      (finSuccEquiv B e (C (algebraMap k B ((eval v H)⁻¹)) * σ f)).Monic) ∧
    Function.Injective (fun g : MvPolynomial (Fin (e + 1)) B ↦ f * g) := by
  sorry

end MvPolynomial
