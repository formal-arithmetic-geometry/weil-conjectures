module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-! # Inverting matrices with shifted degree-lex coefficient support

Source: agent algebra refinement of the finite coefficient solve along ILO VIII
2.3.11--2.3.13, motivated by Bierstone--Milman (1997), Lemma 9.12 and (9.13),
pp.280--281 (blueprint: lem-trf-shift-filtered-matrix-inverse).
The support estimate itself is the agent-written cofactor argument recorded in the DAG,
not an assertion of ILO. All W coordinates precede the weight coordinates.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Matrix

/-- A matrix with nonzero constant determinant and shifted degree-lex support has a
unique two-sided inverse, whose entries obey the same support bound.
Source: agent algebra refinement of ILO VIII 2.3.11--2.3.13; motivating finite solve:
Bierstone--Milman (1997), Lemma 9.12 and (9.13), pp.280--281
(blueprint: lem-trf-shift-filtered-matrix-inverse).

Here `Finsupp.sumElim delta (weights i)` is the concatenated exponent `(delta,u_i)`.
The variable relation `Sum.Lex` puts all W variables before all weight variables.
Negating the strict `Finsupp.DegLex` comparison expresses the weak lower bound.

Proof plan:
1. Embed exponents in the lexicographically ordered integer group by
   theta(delta,v) = (|delta| + |v|, delta, v). This agrees with the stated order on
   natural exponents. Translation preserves comparisons, finite inequalities add,
   common weights cancel, and theta(epsilon,0) is nonnegative.
2. Put D = det A. By lem-weil-pbc-power-series-local-ring, D(0) nonzero in the field
   makes D a unit in the series ring. Choose its scalar inverse h. By
   lem-weil-pbc-matrix-adjugate-identity, B = h times adj(A) is a two-sided inverse.
   Any other inverse C satisfies C = C(AB) = (CA)B = B.
3. For a positive matrix size, expand the (i,j) adjugate entry as the cofactor
   deleting row j and column i, using lem-weil-pbc-matrix-adjugate-identity and
   def-weil-pbc-matrix-determinant. By the finite Cauchy coefficient formula in
   def-weil-pbc-multivariate-power-series, any nonzero coefficient has a nonzero
   summand. It selects a bijection between the remaining rows and columns and
   exponents delta_k summing to delta, with every selected entry coefficient nonzero.
   The size-one empty cofactor contributes only in exponent zero.
4. Add the support inequalities for those factors in the integer group. With U
   the sum of all weights, the result is theta(delta,U-u_j) >= theta(0,U-u_i).
   Add theta(0,u_i+u_j) and cancel theta(0,U), obtaining the desired bound
   theta(delta,u_i) >= theta(0,u_j) for the adjugate entry. Weights may repeat.
5. A nonzero coefficient of h times adj(A) has a nonzero Cauchy summand with
   exponents epsilon + eta = delta. The adjugate bound at eta and the nonnegativity
   of theta(epsilon,0) give the bound at delta. No restriction on h is needed.
6. For size zero the empty matrix is its unique inverse, its determinant is one,
   and the entry condition is vacuous. Zero W variables leave only exponent zero;
   zero weight variables make the support condition automatic. These cases use
   the empty-index conventions of the determinant and series dependency nodes. -/
theorem exists_unique_twoSidedInverse_shiftedDegreeLex
    {L : Type u} [Field L] {m n r : ℕ}
    (weights : Fin r → Fin n →₀ ℕ)
    (A : Matrix (Fin r) (Fin r) (MvPowerSeries (Fin m) L))
    (hdet : MvPowerSeries.constantCoeff (Matrix.det A) ≠ 0)
    (hsupport : ∀ (i j : Fin r) (delta : Fin m →₀ ℕ),
      MvPowerSeries.coeff delta (A i j) ≠ 0 →
        ¬ Finsupp.DegLex (Sum.Lex (· < ·) (· < ·)) (· < ·)
          (Finsupp.sumElim delta (weights i))
          (Finsupp.sumElim (0 : Fin m →₀ ℕ) (weights j))) :
    ∃ B : Matrix (Fin r) (Fin r) (MvPowerSeries (Fin m) L),
      A * B = 1 ∧ B * A = 1 ∧
      (∀ C : Matrix (Fin r) (Fin r) (MvPowerSeries (Fin m) L),
        A * C = 1 → C * A = 1 → C = B) ∧
      ∀ (i j : Fin r) (delta : Fin m →₀ ℕ),
        MvPowerSeries.coeff delta (B i j) ≠ 0 →
          ¬ Finsupp.DegLex (Sum.Lex (· < ·) (· < ·)) (· < ·)
            (Finsupp.sumElim delta (weights i))
            (Finsupp.sumElim (0 : Fin m →₀ ℕ) (weights j)) := by
  sorry

end Matrix
