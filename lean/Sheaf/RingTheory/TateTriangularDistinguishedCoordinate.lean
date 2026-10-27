module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.MvPowerSeries.Rename
import Sheaf.TraceFormula.PolynomialShearLeadingCoefficient

/-!
# Distinguished coordinates for a restricted power series

Source: Conrad, Several approaches to non-archimedean geometry, Definition 1.1.2,
Exercise 1.1.3 and the paragraph preceding Theorem 1.1.5, PDF pp. 3--4.
The coordinate-normalization argument is reconstructed in the DAG, not printed in Conrad.
(blueprint: lem-per-tate-triangular-distinguished-coordinate)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- A nonzero restricted series becomes distinguished in the last variable after an
isometric triangular change of coordinates and multiplication by a unit in the other variables.
Here `m + 1` is the number of variables; `m = 0` includes the one-variable case.
A ring equivalence fixing `constants` is exactly an F-algebra automorphism. Isometry is
expressed by equality of Gauss norms, and the row expansion by equality of every coefficient.
For zero variables the restricted-series ring consists precisely of constants, hence is F.

Source: Conrad, Several approaches to non-archimedean geometry, Definition 1.1.2,
Exercise 1.1.3 and the paragraph preceding Theorem 1.1.5, PDF pp. 3--4;
agent-reconstructed coordinate argument
(blueprint: lem-per-tate-triangular-distinguished-coordinate).

Proof plan:
1. By lem-trf-restricted-series-gauss-completion, the Gauss rings are complete, their
norms are ultrametric and submultiplicative, and regrouping by the last variable is isometric.
Choose a coefficient lambda of maximal nonzero norm and scale f to g = lambda^(-1) f.
The norm-one coefficients of g form a nonzero finite polynomial p. Its remainder h has
norm at most rho < 1: take the maximum of 1/2 and the finitely many coefficient norms in
(1/2,1). Scalar multiplication multiplies the Gauss norm by the scalar absolute value.
2. For nonconstant p, lem-trf-polynomial-shear-leading-coefficient gives positive weights
and a scalar leading coefficient c of norm one in last-variable degree d. For constant p,
use d = 0 and all weights one. With one variable the substitution is the identity.
3. Apply lem-per-tate-banach-substitution to the plus and minus shears. The target Gauss
rings satisfy its completeness and norm hypotheses by the Gauss-completion node and the
coefficientwise scalar identity. Both tuples have norm at most one. The composites fix
constants and variables, hence are identities by uniqueness of substitution. Contractivity
in both directions makes the plus shear isometric. Its action on polynomials is Step 2.
4. Regroup sigma(g) into rows A_j. Isometric regrouping bounds all row norms by one;
A_d = c + e with norm(e) at most rho, and every row above d has norm at most rho.
5. In the complete smaller Gauss ring put q = -c^(-1)e. Its norm is at most rho < 1.
The sums s_k = sum_{i=0}^k q^i are Cauchy, with differences bounded by rho^(k+1).
Their limit s has norm at most one; passing the finite geometric identities to the limit
gives (1-q)s = s(1-q) = 1. Then w = c^(-1)s inverts A_d. Ultrametricity gives norm(A_d)=1,
and submultiplicativity applied to A_d*w=1 gives norm(w)=1.
6. Set v = lambda^(-1)w, a unit with inverse lambda*A_d. The rows of v*sigma(f) are w*A_j.
Thus the d-th row is one, the lower rows have norms at most one, and the entire upper tail
has supremum at most rho < 1. Multiplication by w preserves decay of the row norms.
If d=0 the lower condition is empty; if m=0 no coordinate change is made and v is a scalar.
-/
theorem exists_tate_triangular_distinguished_coordinate
    (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (m : ℕ)
    (f : MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin (m + 1) ↦ (1 : ℝ)))
    (hf : f ≠ 0) :
    ∃ (N : Fin m → ℕ)
      (σ : (MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin (m + 1) ↦ (1 : ℝ))) ≃+*
        (MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin (m + 1) ↦ (1 : ℝ))))
      (v : (MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin m ↦ (1 : ℝ)))ˣ)
      (a : ℕ → MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin m ↦ (1 : ℝ)))
      (d : ℕ),
      (∀ i, 0 < N i) ∧
      (∀ c : F, σ (constants F (m + 1) c) = constants F (m + 1) c) ∧
      (∀ g, MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ ↦ 1) (σ g).val =
        MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ ↦ 1) g.val) ∧
      (∀ i : Fin m,
        (σ ⟨MvPowerSeries.X i.castSucc, MvPowerSeries.isRestricted_monomial _ _ _⟩).val =
          MvPowerSeries.X i.castSucc + MvPowerSeries.X (Fin.last m) ^ N i) ∧
      (σ ⟨MvPowerSeries.X (Fin.last m), MvPowerSeries.isRestricted_monomial _ _ _⟩).val =
        MvPowerSeries.X (Fin.last m) ∧
      (∀ μ : Fin (m + 1) →₀ ℕ,
        MvPowerSeries.coeff μ
            (MvPowerSeries.rename Fin.castSucc (v.val).val * (σ f).val) =
          MvPowerSeries.coeff
            (Finsupp.equivFunOnFinite.symm (fun i : Fin m ↦ μ i.castSucc))
            (a (μ (Fin.last m))).val) ∧
      a d = 1 ∧
      (∀ j : ℕ, j < d →
        MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ ↦ 1) (a j).val ≤ 1) ∧
      (⨆ j : {j : ℕ // d < j},
        MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ ↦ 1) (a j.val).val) < 1 ∧
      (m = 0 → ∀ g, σ g = g) := by
  sorry

end RestrictedSeries
