module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Algebra.DirectSum.Basic

@[expose] public section

universe v

open DirectSum

namespace AlgebraicGeometry

open Classical in
/-- A finite graded Rees module is generated from any sufficiently high single degree.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OA, proof of (1).
(blueprint: lem-weil-pbc-finite-rees-module-single-degree-generation)

Proof: Choose finitely many generators over Rees(I), and replace each by its finitely
many homogeneous components. This still generates: the enlarged span contains the
original generators. Let c0 be the maximum of their degrees, or zero if there are none.
For a nonzero a, convolution identifies the action of a*t^k on degree d with L k d a.
Zero monomials act by zero and may be omitted. Associativity multiplies coefficients;
the degree-zero formula identifies constants with the given A-action. No formula for
L k d 0 is needed: its extra images can only enlarge the span under consideration.
For c >= c0 and a homogeneous vector in degree c+k, expand it using these homogeneous
generators and project the expression to degree c+k. A generator of degree d contributes
only coefficients in I^(c+k-d). Since d <= c, this ideal equals I^k * I^(c-d).
Each coefficient is a finite sum of products a*b with a in I^k and b in I^(c-d).
Associativity moves b onto the degree-d generator, producing a vector in degree c,
and the remaining action is L k c a. Thus these images span the whole degree c+k.
The reverse containment is automatic. Empty generating sets, k = 0, c = 0, I = 0,
and I = A are included in the same argument. -/
theorem finite_rees_module_single_degree_generation
    (A : Type v) [CommRing A] (I : Ideal A)
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module A (M n)]
    (L : ∀ (k n : ℕ) (a : A), a ∈ I ^ k → M n →ₗ[A] M (n + k))
    (hzero : ∀ (n : ℕ) (a : A) (ha : a ∈ I ^ 0) (x : M n),
      L 0 n a ha x = a • x)
    (mod : Module (reesAlgebra I) (⨁ n, M n))
    (hfin : @Module.Finite (reesAlgebra I) (⨁ n, M n) _ _ mod)
    (hact : ∀ (b : reesAlgebra I) (x : ⨁ n, M n),
      @SMul.smul _ _ mod.toSMul b x =
        ∑ k ∈ b.val.support, ∑ n ∈ x.support,
          DirectSum.of M (n + k) (L k n (b.val.coeff k) (b.property k) (x n))) :
    ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c → ∀ k : ℕ,
      Submodule.span A (Set.range (fun p : (↥(I ^ k)) × M c ↦ L k c p.1 p.1.property p.2)) =
        (⊤ : Submodule A (M (c + k))) := by
  sorry

end AlgebraicGeometry
