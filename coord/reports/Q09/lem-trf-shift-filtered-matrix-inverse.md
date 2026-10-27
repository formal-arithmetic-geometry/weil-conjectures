## Worker report

The module `Sheaf.RingTheory.ShiftFilteredMatrixInverse` states
`Matrix.exists_unique_twoSidedInverse_shiftedDegreeLex`, with its entire proof
postponed as `sorry`. No definitions, extra nodes, dependency repairs, or statement
corrections are needed. The original node is preserved except for `lean`.

Hypothesis and conclusion correspondence:

- The field L is `{L : Type u} [Field L]`, with arbitrary coefficient universe u.
- The three nonnegative integers are `{m n r : ℕ}`. Matrix indices are `Fin r`.
- The r indexed weights in N^n are `weights : Fin r → Fin n →₀ ℕ`. For finite
  coordinate sets, finite support excludes no exponent vector. There is no
  positivity or distinctness hypothesis on these weights.
- The matrix over L[[W_1,...,W_m]] is
  `A : Matrix (Fin r) (Fin r) (MvPowerSeries (Fin m) L)`.
- Its specified determinant and nonzero constant value are exactly
  `hdet : MvPowerSeries.constantCoeff (Matrix.det A) ≠ 0`.
- `Finsupp.sumElim delta (weights i)` concatenates the W exponent and row weight.
  Its coordinate type is `Fin m ⊕ Fin n`. The explicit index relation
  `Sum.Lex (· < ·) (· < ·)` puts every W coordinate before every weight coordinate
  and uses increasing indices within each block. This is the order-preserving
  identification with the node's N^(m+n).
- `Finsupp.DegLex` compares total degree first, then the earliest unequal
  coordinate (Mathlib's definition is `Prod.Lex` on `(x.degree,x)`, with the
  second component compared by `Finsupp.Lex`, hence by `Pi.Lex`). The expression
  `¬ Finsupp.DegLex ... (sumElim delta (weights i)) (sumElim 0 (weights j))`
  says exactly `(delta,u_i) ≥ (0,u_j)`: the negation of strict less than in this
  total order. It includes equality. `hsupport` imposes it precisely when the
  corresponding `MvPowerSeries.coeff delta (A i j)` is nonzero, for all i,j,delta.
- `∃ B : Matrix ...` asserts an inverse in the same series matrix ring.
  `A * B = 1 ∧ B * A = 1` gives both inverse identities.
- `∀ C : Matrix ..., A * C = 1 → C * A = 1 → C = B` gives uniqueness among
  ALL two-sided inverses, without assuming any support condition on C.
- The last universally quantified implication repeats exactly `hsupport` with B
  replacing A. Thus it is the claimed coefficient estimate for the inverse.

Dependency declarations, all read with full signatures and surrounding documentation:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (available through the
  imports), the commutative ring/division ring structure. No characteristic restriction.
- `def-weil-matrix`: `Matrix`, Mathlib.LinearAlgebra.Matrix.Defs, the family
  `Fin r → Fin r → MvPowerSeries (Fin m) L`.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  Mathlib.RingTheory.MvPowerSeries.Basic, the coefficient family on Finsupp exponents;
  also its `coeff` and `constantCoeff` declarations.
- `def-weil-pbc-matrix-determinant`: `Matrix.det`,
  Mathlib.LinearAlgebra.Matrix.Determinant.Basic, with its Leibniz formula
  `Matrix.det_apply` and empty determinant convention.
- Proof-only import Mathlib.RingTheory.MvPowerSeries.Inverse provides
  `MvPowerSeries.isUnit_iff_constantCoeff` and its local-ring instance for
  `lem-weil-pbc-power-series-local-ring`.
- Proof-only import Mathlib.LinearAlgebra.Matrix.Adjugate provides
  `Matrix.adjugate_mul`, `Matrix.mul_adjugate`, and
  `Matrix.adjugate_fin_succ_eq_det_submatrix` for
  `lem-weil-pbc-matrix-adjugate-identity`.
- The comparison and concatenation use existing Mathlib definitions:
  `Finsupp.DegLex` from Mathlib.Data.Finsupp.MonomialOrder.DegLex,
  `Finsupp.Lex`/`Pi.Lex`, `Sum.Lex`, and `Finsupp.sumElim`.

The theorem docstring carries the node's complete six-step natural-language proof:
integer-group translation and cancellation; the unit determinant and adjugate;
nonzero summands in finite cofactor/Cauchy expansions; cancellation of total
weights; scalar inverse multiplication; and the empty-index cases. I read ILO
VIII pp.93--94 (PDF pages 99--100), including 2.3.11--2.3.13: these discuss the
resolution route, not the support estimate. The module explicitly attributes the
estimate to the agent algebra argument, as the node does, rather than to ILO.

Edge cases checked before writing and rechecked against the signature:

- r=0: the matrix type has exactly one element, the determinant is one, both
  products are the empty identity, uniqueness applies, and no entry is tested.
- m=0: the sole W exponent is zero and power series in no variables are L.
  The weight comparison is retained, not erased by an assumption m>0.
- n=0: all weights are empty; `(delta,())` is never below `(0,())`, so both
  support bounds are automatic. Also m=n=0 causes no nonempty-index requirement.
- r=1: the adjugate cofactor is the empty determinant and the statement still
  requires only a nonzero constant scalar determinant.
- Repeated weights are permitted by the unrestricted weights family and weak
  comparison; at equal weights every nonnegative W exponent is allowed.
- With m=n=1, row weight 0 and column weight 1, delta=0 is forbidden, but
  delta=1 is allowed: total degrees tie and W precedes the last coordinate.
  This checks the coordinate priority and orientation. For weights (0,1), the
  matrix [[1,W],[1,1]] and inverse (1-W)^(-1)[[1,-W],[-1,1]] respect that bound.
- Arbitrary field characteristics and arbitrary u remain allowed.

Searches (2026-10-24; raw wrapper results are in sandbox searches.jsonl):

- msearch leanfinder, query `inverse of formal power series matrix preserves
  shifted degree lexicographic coefficient support`: eight hits, scalar series
  inverse coefficient formulas and the matrix-polynomial coefficient equivalence;
  none gives shifted support preservation for inverse matrices.
- msearch loogle, query `MonomialOrder.degLex, Matrix.inv`: zero hits.
- msearch grep, query `degLex|degreeLex|gradedLex`: 18 hits, locating the existing
  Mathlib degree-lex definitions used here, not this matrix theorem.
- msearch leansearch, query `inverse matrix of formal power series preserves
  shifted degree lexicographic support`: eight hits on scalar inverses and
  coefficient formulas, no exact statement.
- msearch grep, query `shift.*[Ff]iltrat|filtrat.*inv|monomial.*matrix` in
  RingTheory: zero hits.
- rg of lean/WeilConjectures and lean/Sheaf for shifted filtration and degree-lex
  terms found homogeneous division, formal initial diagrams, and coefficient
  projection consumers, not this theorem. Reading FormalInitialDiagram,
  SupportedHomogeneousDivision and RegularHilbertCoefficientDatum confirmed
  their use of the same Mathlib order (the latter explicitly uses Sum.Lex).
- rg for the node id in lean/WeilConjectures and dag/lean_names_upstream.json
  gave no existing declaration. An exact-name/concept search for
  `exists.*[Ii]nverse.*[Ss]hift|shiftedDegreeLex|twoSidedInverse` in Mathlib,
  lean/WeilConjectures and lean/Sheaf gave no matches.

Validation: scompile.py compiled the file both as sandbox and as its library
module, with no errors or unexpected warnings (6.5 and 3.3 seconds respectively).
No statement fault or dispute was found.

## Second reading by Q09

This is the worker's second pass, not an independent agent review; the dispatcher
forbids starting other agents and assigns independent review to the maintainer.
I reopened the original node and complete Lean file and checked every binder and
conjunct against the correspondence above. In particular, the two-sided inverse
uniqueness quantifies over C without support assumptions; the weak lower bound
is the negation of strict less, not the reverse inequality; total degree includes
both blocks; and Sum.Lex compares W first. The index types include the zero-size
cases and no distinctness of weights was added. The proof-only imports cover all
stated proof dependencies. No mismatch was found and no correction was made.
