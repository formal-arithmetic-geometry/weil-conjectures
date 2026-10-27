module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.Submodule.Defs

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Nonzero-point evaluations detect vector Laurent coefficients modulo a subspace

Source: Milne, Algebraic Groups (2017), Proposition 1.11 and Remark 1.14, printed p. 10;
the vector-coefficient quotient argument in the DAG
(blueprint: lem-sfb-laurent-vector-evaluation-test).

The existing type `(Fin r → ℤ) →₀ V` is exactly a finite formal sum of vectors indexed by
integer exponent vectors. Evaluation is written using `Finsupp.sum` and scalar multiplication.
-/

@[expose] public section

universe u v

namespace Finsupp

/-- A finite vector Laurent sum takes values in a subspace on every nonzero tuple if and
only if every coefficient belongs to that subspace. There is no dimension restriction on
the vector space. Empty support and zero variables are allowed.

Source: Milne, Algebraic Groups (2017), Proposition 1.11 and Remark 1.14, printed p. 10;
the vector-coefficient quotient argument in the DAG
(blueprint: lem-sfb-laurent-vector-evaluation-test).

Proof plan:
1. If the support is empty, coefficients and evaluations are zero. Otherwise pass to
   `U = V ⧸ W` with quotient map `q`; linearity gives zero for every evaluated Laurent
   sum of the vectors `q (P e)`. A coefficient has zero image exactly when it lies in `W`.
2. For each coordinate choose `a i = 1 + max ({0} ∪ {-e i | e ∈ P.support})`.
   After applying any linear functional `λ : U →ₗ[k] k`, shift every exponent by `a`.
   This gives an ordinary scalar multivariate polynomial with strictly positive exponents
   in each coordinate. It vanishes at tuples with a zero coordinate term by term, and at
   nonzero tuples by the evaluated quotient identity and integer-power addition.
   Apply `MvPolynomial.funext` (lem-sfb-mvpolynomial-infinite-evaluation) to conclude
   that this polynomial is zero. The shift is injective, so every `λ (q (P e))` is zero.
3. If a quotient coefficient were nonzero, `Module.Projective.exists_dual_ne_zero`
   (lem-weil-pbc-vector-space-dual-separates) would give a functional nonzero on it,
   a contradiction. Outside the support the coefficients are already zero.
4. Conversely, a subspace contains scalar multiples and finite sums of its elements,
   so coefficient membership implies evaluation membership. For `r = 0` both tuple
   types are singletons, the monomial product is `1`, and evaluation is the unique
   coefficient; the same argument includes this case. -/
theorem laurent_sum_mem_submodule_iff
    {k : Type u} [Field k] [Infinite k]
    {V : Type v} [AddCommGroup V] [Module k V]
    (r : ℕ) (W : Submodule k V) (P : (Fin r → ℤ) →₀ V) :
    (∀ t : Fin r → kˣ,
      P.sum (fun e x ↦ (∏ i : Fin r, (t i : k) ^ e i) • x) ∈ W) ↔
      ∀ e : Fin r → ℤ, P e ∈ W := by
  sorry

end Finsupp
